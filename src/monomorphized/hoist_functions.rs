//! Hoist closed anonymous Mono functions into named top-level helpers.
//!
//! This pass runs late in the pipeline, after JavaScript rewriting and the last
//! round of Mono cleanup.  By that point, any remaining `Abs` nodes that do not
//! capture relative variables are safe to turn into `Named` references backed by
//! synthetic `Decl::Val` helpers.  That keeps CJR lowering from tripping over
//! anonymous functions while preserving semantics.

use crate::error_types::Located;
use crate::monomorphized::environment::pat_binds_n;
use crate::monomorphized::{
    DbMode, Decl, Exp, File, JavaScriptMode, LocDecl, LocExp, LocPat, LocTyp, Pat, Policy,
    QueryMeta, Sidedness, Typ,
};

pub fn hoist_closed_functions(file: File) -> File {
    let (decls, exports) = file;
    let mut pass = HoistClosedFunctions::new(&decls, &exports);
    let mut out = Vec::with_capacity(decls.len());
    for decl in decls {
        pass.rewrite_decl_into(decl, &mut out);
    }
    (out, exports)
}

struct HoistClosedFunctions {
    next_name: usize,
}

impl HoistClosedFunctions {
    fn new(decls: &[LocDecl], exports: &[(usize, Sidedness, DbMode)]) -> Self {
        Self {
            next_name: max_name_in_file(decls, exports) + 1,
        }
    }

    fn fresh_name(&mut self) -> usize {
        let n = self.next_name;
        self.next_name += 1;
        n
    }

    fn fresh_name_avoiding(&mut self, exp: &LocExp) -> usize {
        let mut n = self.fresh_name();
        while exp_mentions_name(exp, n) {
            n = self.fresh_name();
        }
        n
    }

    fn rewrite_decl_into(&mut self, decl: LocDecl, out: &mut Vec<LocDecl>) {
        let span = decl.span.clone();
        let mut helpers = Vec::new();
        let node = match decl.node {
            Decl::Val(x, n, t, e, sql_name) => {
                let helper_sql_name = (sql_name == "<script>").then_some(sql_name.as_str());
                Decl::Val(
                    x,
                    n,
                    t,
                    self.rewrite_exp(e, &mut helpers, helper_sql_name),
                    sql_name,
                )
            }
            Decl::ValRec(vis) => Decl::ValRec(
                vis.into_iter()
                    .map(|(x, n, t, e, sql_name)| {
                        let helper_sql_name = (sql_name == "<script>").then_some(sql_name.as_str());
                        (
                            x,
                            n,
                            t,
                            self.rewrite_exp(e, &mut helpers, helper_sql_name),
                            sql_name,
                        )
                    })
                    .collect(),
            ),
            Decl::Table(name, xts, pe, ce) => Decl::Table(
                name,
                xts,
                self.rewrite_exp(pe, &mut helpers, None),
                self.rewrite_exp(ce, &mut helpers, None),
            ),
            Decl::View(name, xts, e) => {
                Decl::View(name, xts, self.rewrite_exp(e, &mut helpers, None))
            }
            Decl::Task(e1, e2) => Decl::Task(
                self.rewrite_exp(e1, &mut helpers, None),
                self.rewrite_exp(e2, &mut helpers, None),
            ),
            Decl::Policy(pol) => Decl::Policy(self.rewrite_policy(pol, &mut helpers, None)),
            other => other,
        };
        out.extend(helpers);
        out.push(Located::new(node, span));
    }

    fn rewrite_policy(
        &mut self,
        pol: Policy,
        helpers: &mut Vec<LocDecl>,
        helper_sql_name: Option<&str>,
    ) -> Policy {
        match pol {
            Policy::Client(e) => Policy::Client(self.rewrite_exp(e, helpers, helper_sql_name)),
            Policy::Insert(e) => Policy::Insert(self.rewrite_exp(e, helpers, helper_sql_name)),
            Policy::Delete(e) => Policy::Delete(self.rewrite_exp(e, helpers, helper_sql_name)),
            Policy::Update(e) => Policy::Update(self.rewrite_exp(e, helpers, helper_sql_name)),
            Policy::Sequence(e) => Policy::Sequence(self.rewrite_exp(e, helpers, helper_sql_name)),
        }
    }

    fn rewrite_exp(
        &mut self,
        exp: LocExp,
        helpers: &mut Vec<LocDecl>,
        helper_sql_name: Option<&str>,
    ) -> LocExp {
        self.rewrite_exp_with_context(exp, helpers, helper_sql_name, false)
    }

    fn rewrite_exp_with_context(
        &mut self,
        exp: LocExp,
        helpers: &mut Vec<LocDecl>,
        helper_sql_name: Option<&str>,
        suppress_root_hoist: bool,
    ) -> LocExp {
        let span = exp.span.clone();
        let node = match exp.node {
            Exp::Prim(_) | Exp::Rel(_) | Exp::Named(_) | Exp::Ffi(_, _) => exp.node,
            Exp::Con(dk, pc, arg) => Exp::Con(
                dk,
                pc,
                arg.map(|inner| {
                    Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, false))
                }),
            ),
            Exp::None(t) => Exp::None(t),
            Exp::Some(t, inner) => Exp::Some(
                t,
                Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, false)),
            ),
            Exp::FfiApp(module, name, args) => Exp::FfiApp(
                module,
                name,
                args.into_iter()
                    .map(|(arg, typ)| {
                        (
                            self.rewrite_exp_with_context(arg, helpers, helper_sql_name, false),
                            typ,
                        )
                    })
                    .collect(),
            ),
            Exp::App(f, arg) => Exp::App(
                Box::new(self.rewrite_exp_with_context(*f, helpers, helper_sql_name, false)),
                Box::new(self.rewrite_exp_with_context(*arg, helpers, helper_sql_name, false)),
            ),
            Exp::Abs(x, dom, ran, body) => {
                let body = self.rewrite_exp_with_context(*body, helpers, helper_sql_name, false);
                let abs = Located::new(
                    Exp::Abs(x.clone(), dom.clone(), ran.clone(), Box::new(body)),
                    span.clone(),
                );
                if !suppress_root_hoist && should_hoist_abs(&abs) {
                    let n = self.fresh_name_avoiding(&abs);
                    let helper_name = format!("lam_{n}");
                    let helper_sql_name = helper_sql_name.unwrap_or(helper_name.as_str());
                    let helper_typ =
                        Located::new(Typ::Fun(Box::new(dom), Box::new(ran)), span.clone());
                    if std::env::var("URWEB_DEBUG_HOIST_TYPES").ok().as_deref() == Some("1")
                        && (span.file.ends_with("/demo/metaform.ur")
                            || span.file.ends_with("/lib/ur/top.ur"))
                    {
                        eprintln!(
                            "URWEB_DEBUG_HOIST_TYPES {}:{} helper={} typ={:?} abs={:?}",
                            span.file, span.first.line, helper_name, helper_typ.node, abs.node
                        );
                    }
                    helpers.push(Located::new(
                        Decl::Val(
                            helper_name.clone(),
                            n,
                            helper_typ,
                            abs,
                            helper_sql_name.to_string(),
                        ),
                        span.clone(),
                    ));
                    Exp::Named(n)
                } else {
                    abs.node
                }
            }
            Exp::Unop(op, inner) => Exp::Unop(
                op,
                Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, false)),
            ),
            Exp::Binop(kind, op, left, right) => Exp::Binop(
                kind,
                op,
                Box::new(self.rewrite_exp_with_context(*left, helpers, helper_sql_name, false)),
                Box::new(self.rewrite_exp_with_context(*right, helpers, helper_sql_name, false)),
            ),
            Exp::Record(fields) => Exp::Record(
                fields
                    .into_iter()
                    .map(|(name, inner, typ)| {
                        (
                            name,
                            self.rewrite_exp_with_context(inner, helpers, helper_sql_name, false),
                            typ,
                        )
                    })
                    .collect(),
            ),
            Exp::Field(inner, field) => Exp::Field(
                Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, true)),
                field,
            ),
            Exp::Case(disc, arms, meta) => Exp::Case(
                Box::new(self.rewrite_exp_with_context(*disc, helpers, helper_sql_name, false)),
                arms.into_iter()
                    .map(|(pat, arm)| {
                        (
                            pat,
                            self.rewrite_exp_with_context(arm, helpers, helper_sql_name, false),
                        )
                    })
                    .collect(),
                meta,
            ),
            Exp::Strcat(left, right) => Exp::Strcat(
                Box::new(self.rewrite_exp_with_context(*left, helpers, helper_sql_name, false)),
                Box::new(self.rewrite_exp_with_context(*right, helpers, helper_sql_name, false)),
            ),
            Exp::Error(inner, typ) => Exp::Error(
                Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, false)),
                typ,
            ),
            Exp::ReturnBlob { blob, mime_type, t } => Exp::ReturnBlob {
                blob: blob.map(|inner| {
                    Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, false))
                }),
                mime_type: Box::new(self.rewrite_exp_with_context(
                    *mime_type,
                    helpers,
                    helper_sql_name,
                    false,
                )),
                t,
            },
            Exp::Redirect(inner, typ) => Exp::Redirect(
                Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, false)),
                typ,
            ),
            Exp::Write(inner) => Exp::Write(Box::new(self.rewrite_exp_with_context(
                *inner,
                helpers,
                helper_sql_name,
                false,
            ))),
            Exp::Seq(left, right) => Exp::Seq(
                Box::new(self.rewrite_exp_with_context(*left, helpers, helper_sql_name, false)),
                Box::new(self.rewrite_exp_with_context(*right, helpers, helper_sql_name, false)),
            ),
            Exp::Let(name, typ, bound, body) => Exp::Let(
                name,
                typ,
                Box::new(self.rewrite_exp_with_context(*bound, helpers, helper_sql_name, false)),
                Box::new(self.rewrite_exp_with_context(*body, helpers, helper_sql_name, false)),
            ),
            Exp::Closure(n, envs) => Exp::Closure(
                n,
                envs.into_iter()
                    .map(|inner| {
                        self.rewrite_exp_with_context(inner, helpers, helper_sql_name, false)
                    })
                    .collect(),
            ),
            Exp::Query(QueryMeta {
                exps,
                tables,
                state,
                query,
                body,
                initial,
            }) => Exp::Query(QueryMeta {
                exps,
                tables,
                state,
                query: Box::new(self.rewrite_exp_with_context(
                    *query,
                    helpers,
                    helper_sql_name,
                    false,
                )),
                body: Box::new(self.rewrite_exp_with_context(
                    *body,
                    helpers,
                    helper_sql_name,
                    false,
                )),
                initial: Box::new(self.rewrite_exp_with_context(
                    *initial,
                    helpers,
                    helper_sql_name,
                    false,
                )),
            }),
            Exp::Dml(inner, mode) => Exp::Dml(
                Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, false)),
                mode,
            ),
            Exp::Nextval(inner) => Exp::Nextval(Box::new(self.rewrite_exp_with_context(
                *inner,
                helpers,
                helper_sql_name,
                false,
            ))),
            Exp::Setval(seq, count) => Exp::Setval(
                Box::new(self.rewrite_exp_with_context(*seq, helpers, helper_sql_name, false)),
                Box::new(self.rewrite_exp_with_context(*count, helpers, helper_sql_name, false)),
            ),
            Exp::Uurlify(inner, typ, flag) => Exp::Uurlify(
                Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, false)),
                typ,
                flag,
            ),
            Exp::JavaScript(mode, inner) => Exp::JavaScript(
                map_javascript_mode(mode, helpers, self),
                Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, false)),
            ),
            Exp::SignalReturn(inner) => Exp::SignalReturn(Box::new(self.rewrite_exp_with_context(
                *inner,
                helpers,
                helper_sql_name,
                false,
            ))),
            Exp::SignalBind(left, right) => Exp::SignalBind(
                Box::new(self.rewrite_exp_with_context(*left, helpers, helper_sql_name, false)),
                Box::new(self.rewrite_exp_with_context(*right, helpers, helper_sql_name, false)),
            ),
            Exp::SignalSource(inner) => Exp::SignalSource(Box::new(self.rewrite_exp_with_context(
                *inner,
                helpers,
                helper_sql_name,
                false,
            ))),
            Exp::ServerCall(inner, typ, effect, failure_mode) => Exp::ServerCall(
                Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, false)),
                typ,
                effect,
                failure_mode,
            ),
            Exp::Recv(inner, typ) => Exp::Recv(
                Box::new(self.rewrite_exp_with_context(*inner, helpers, helper_sql_name, false)),
                typ,
            ),
            Exp::Sleep(inner) => Exp::Sleep(Box::new(self.rewrite_exp_with_context(
                *inner,
                helpers,
                helper_sql_name,
                false,
            ))),
            Exp::Spawn(inner) => Exp::Spawn(Box::new(self.rewrite_exp_with_context(
                *inner,
                helpers,
                helper_sql_name,
                false,
            ))),
        };
        Located::new(node, span)
    }
}

fn map_javascript_mode(
    mode: JavaScriptMode,
    helpers: &mut Vec<LocDecl>,
    pass: &mut HoistClosedFunctions,
) -> JavaScriptMode {
    match mode {
        JavaScriptMode::Attribute => JavaScriptMode::Attribute,
        JavaScriptMode::Script => JavaScriptMode::Script,
        JavaScriptMode::Source(typ) => {
            let _ = helpers;
            let _ = pass;
            JavaScriptMode::Source(typ)
        }
    }
}

fn should_hoist_abs(abs: &LocExp) -> bool {
    let Exp::Abs(_, dom, ran, _) = &abs.node else {
        return false;
    };
    !is_spurious_unit_thunk(dom, ran) && !exp_has_free_rel(abs)
}

fn is_spurious_unit_thunk(dom: &LocTyp, ran: &LocTyp) -> bool {
    matches!(&dom.node, Typ::Record(fields) if fields.is_empty())
        && !matches!(&ran.node, Typ::Fun(_, _))
}

fn exp_has_free_rel(exp: &LocExp) -> bool {
    exp_has_free_rel_at_depth(exp, 0)
}

fn exp_has_free_rel_at_depth(exp: &LocExp, depth: usize) -> bool {
    match &exp.node {
        Exp::Rel(n) => *n >= depth,
        Exp::Abs(_, _, _, body) => exp_has_free_rel_at_depth(body, depth + 1),
        Exp::Let(_, _, bound, body) => {
            exp_has_free_rel_at_depth(bound, depth) || exp_has_free_rel_at_depth(body, depth + 1)
        }
        Exp::Case(disc, arms, _) => {
            exp_has_free_rel_at_depth(disc, depth)
                || arms
                    .iter()
                    .any(|(pat, arm)| exp_has_free_rel_at_depth(arm, depth + pat_binds_n(pat)))
        }
        Exp::Query(QueryMeta {
            query,
            body,
            initial,
            ..
        }) => {
            exp_has_free_rel_at_depth(query, depth)
                || exp_has_free_rel_at_depth(body, depth + 2)
                || exp_has_free_rel_at_depth(initial, depth)
        }
        Exp::App(f, arg)
        | Exp::Strcat(f, arg)
        | Exp::Seq(f, arg)
        | Exp::Binop(_, _, f, arg)
        | Exp::SignalBind(f, arg)
        | Exp::Setval(f, arg) => {
            exp_has_free_rel_at_depth(f, depth) || exp_has_free_rel_at_depth(arg, depth)
        }
        Exp::Write(inner)
        | Exp::Unop(_, inner)
        | Exp::Field(inner, _)
        | Exp::JavaScript(_, inner)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::Nextval(inner)
        | Exp::Sleep(inner)
        | Exp::Spawn(inner)
        | Exp::Uurlify(inner, _, _)
        | Exp::Dml(inner, _)
        | Exp::Redirect(inner, _)
        | Exp::Error(inner, _)
        | Exp::ServerCall(inner, _, _, _)
        | Exp::Recv(inner, _) => exp_has_free_rel_at_depth(inner, depth),
        Exp::Con(_, _, Some(inner)) | Exp::Some(_, inner) => {
            exp_has_free_rel_at_depth(inner, depth)
        }
        Exp::FfiApp(_, _, args) => args
            .iter()
            .any(|(arg, _)| exp_has_free_rel_at_depth(arg, depth)),
        Exp::Record(fields) => fields
            .iter()
            .any(|(_, inner, _)| exp_has_free_rel_at_depth(inner, depth)),
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            blob.as_ref()
                .is_some_and(|inner| exp_has_free_rel_at_depth(inner, depth))
                || exp_has_free_rel_at_depth(mime_type, depth)
        }
        Exp::Closure(_, envs) => envs
            .iter()
            .any(|inner| exp_has_free_rel_at_depth(inner, depth)),
        Exp::Prim(_) | Exp::Named(_) | Exp::Ffi(_, _) | Exp::None(_) => false,
        Exp::Con(_, _, None) => false,
    }
}

fn max_name_in_file(decls: &[LocDecl], exports: &[(usize, Sidedness, DbMode)]) -> usize {
    let mut max_name = 0usize;
    for decl in decls {
        max_name_in_decl(&decl.node, &mut max_name);
    }
    for (id, _, _) in exports {
        update_max_name(&mut max_name, *id);
    }
    max_name
}

fn update_max_name(max_name: &mut usize, n: usize) {
    *max_name = (*max_name).max(n);
}

fn max_name_in_decl(decl: &Decl, max_name: &mut usize) {
    match decl {
        Decl::Datatype(dts) => {
            for dt in dts {
                update_max_name(max_name, dt.id);
                for (_, constructor_id, _) in &dt.constrs {
                    update_max_name(max_name, *constructor_id);
                }
            }
        }
        Decl::Val(_, n, _, exp, _) => {
            update_max_name(max_name, *n);
            max_name_in_exp(exp, max_name);
        }
        Decl::ValRec(bindings) => {
            for (_, n, _, exp, _) in bindings {
                update_max_name(max_name, *n);
                max_name_in_exp(exp, max_name);
            }
        }
        Decl::Export(_, _, n, _, _, _) => update_max_name(max_name, *n),
        Decl::Database {
            expunge,
            initialize,
            ..
        } => {
            update_max_name(max_name, *expunge);
            update_max_name(max_name, *initialize);
        }
        Decl::OnError(n) => update_max_name(max_name, *n),
        Decl::Task(e1, e2) => {
            max_name_in_exp(e1, max_name);
            max_name_in_exp(e2, max_name);
        }
        Decl::Table(_, _, pe, ce) => {
            max_name_in_exp(pe, max_name);
            max_name_in_exp(ce, max_name);
        }
        Decl::View(_, _, e) => max_name_in_exp(e, max_name),
        Decl::Policy(pol) => match pol {
            Policy::Client(e)
            | Policy::Insert(e)
            | Policy::Delete(e)
            | Policy::Update(e)
            | Policy::Sequence(e) => max_name_in_exp(e, max_name),
        },
        _ => {}
    }
}

fn max_name_in_exp(exp: &LocExp, max_name: &mut usize) {
    match &exp.node {
        Exp::Named(n) => update_max_name(max_name, *n),
        Exp::Closure(n, envs) => {
            update_max_name(max_name, *n);
            for inner in envs {
                max_name_in_exp(inner, max_name);
            }
        }
        Exp::Con(_, crate::monomorphized::PatCon::Var(n), maybe_body) => {
            update_max_name(max_name, *n);
            if let Some(body) = maybe_body {
                max_name_in_exp(body, max_name);
            }
        }
        Exp::Con(_, _, Some(body)) => max_name_in_exp(body, max_name),
        Exp::Abs(_, _, _, body)
        | Exp::Write(body)
        | Exp::Unop(_, body)
        | Exp::Field(body, _)
        | Exp::JavaScript(_, body)
        | Exp::SignalReturn(body)
        | Exp::SignalSource(body)
        | Exp::Nextval(body)
        | Exp::Sleep(body)
        | Exp::Spawn(body)
        | Exp::Uurlify(body, _, _)
        | Exp::Dml(body, _)
        | Exp::Redirect(body, _)
        | Exp::Error(body, _)
        | Exp::ServerCall(body, _, _, _)
        | Exp::Recv(body, _) => max_name_in_exp(body, max_name),
        Exp::Some(_, body) => max_name_in_exp(body, max_name),
        Exp::App(f, arg)
        | Exp::Strcat(f, arg)
        | Exp::Seq(f, arg)
        | Exp::Binop(_, _, f, arg)
        | Exp::SignalBind(f, arg)
        | Exp::Setval(f, arg) => {
            max_name_in_exp(f, max_name);
            max_name_in_exp(arg, max_name);
        }
        Exp::Let(_, _, bound, body) => {
            max_name_in_exp(bound, max_name);
            max_name_in_exp(body, max_name);
        }
        Exp::FfiApp(_, _, args) => {
            for (arg, _) in args {
                max_name_in_exp(arg, max_name);
            }
        }
        Exp::Record(fields) => {
            for (_, inner, _) in fields {
                max_name_in_exp(inner, max_name);
            }
        }
        Exp::Case(disc, arms, _) => {
            max_name_in_exp(disc, max_name);
            for (pat, arm) in arms {
                max_name_in_pat(pat, max_name);
                max_name_in_exp(arm, max_name);
            }
        }
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            if let Some(inner) = blob {
                max_name_in_exp(inner, max_name);
            }
            max_name_in_exp(mime_type, max_name);
        }
        Exp::Query(QueryMeta {
            query,
            body,
            initial,
            ..
        }) => {
            max_name_in_exp(query, max_name);
            max_name_in_exp(body, max_name);
            max_name_in_exp(initial, max_name);
        }
        Exp::Prim(_) | Exp::Rel(_) | Exp::Ffi(_, _) | Exp::None(_) | Exp::Con(_, _, None) => {}
    }
}

fn max_name_in_pat(pat: &LocPat, max_name: &mut usize) {
    match &pat.node {
        Pat::Con(_, crate::monomorphized::PatCon::Var(n), inner) => {
            update_max_name(max_name, *n);
            if let Some(inner) = inner {
                max_name_in_pat(inner, max_name);
            }
        }
        Pat::Con(_, _, Some(inner)) | Pat::Some(_, inner) => max_name_in_pat(inner, max_name),
        Pat::Record(fields) => {
            for (_, inner, _) in fields {
                max_name_in_pat(inner, max_name);
            }
        }
        Pat::Var(_, _) | Pat::Prim(_) | Pat::Con(_, _, None) | Pat::None(_) => {}
    }
}

fn exp_mentions_name(exp: &LocExp, target: usize) -> bool {
    match &exp.node {
        Exp::Named(n) => *n == target,
        Exp::Closure(n, envs) => {
            *n == target || envs.iter().any(|inner| exp_mentions_name(inner, target))
        }
        Exp::Con(_, crate::monomorphized::PatCon::Var(n), maybe_body) => {
            *n == target
                || maybe_body
                    .as_ref()
                    .is_some_and(|body| exp_mentions_name(body, target))
        }
        Exp::Con(_, _, Some(body))
        | Exp::Some(_, body)
        | Exp::Abs(_, _, _, body)
        | Exp::Write(body)
        | Exp::Unop(_, body)
        | Exp::Field(body, _)
        | Exp::JavaScript(_, body)
        | Exp::SignalReturn(body)
        | Exp::SignalSource(body)
        | Exp::Nextval(body)
        | Exp::Sleep(body)
        | Exp::Spawn(body)
        | Exp::Uurlify(body, _, _)
        | Exp::Dml(body, _)
        | Exp::Redirect(body, _)
        | Exp::Error(body, _)
        | Exp::ServerCall(body, _, _, _)
        | Exp::Recv(body, _) => exp_mentions_name(body, target),
        Exp::App(f, arg)
        | Exp::Strcat(f, arg)
        | Exp::Seq(f, arg)
        | Exp::Binop(_, _, f, arg)
        | Exp::SignalBind(f, arg)
        | Exp::Setval(f, arg) => exp_mentions_name(f, target) || exp_mentions_name(arg, target),
        Exp::Let(_, _, bound, body) => {
            exp_mentions_name(bound, target) || exp_mentions_name(body, target)
        }
        Exp::FfiApp(_, _, args) => args.iter().any(|(arg, _)| exp_mentions_name(arg, target)),
        Exp::Record(fields) => fields
            .iter()
            .any(|(_, inner, _)| exp_mentions_name(inner, target)),
        Exp::Case(disc, arms, _) => {
            exp_mentions_name(disc, target)
                || arms.iter().any(|(pat, arm)| {
                    pat_mentions_name(pat, target) || exp_mentions_name(arm, target)
                })
        }
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            blob.as_ref()
                .is_some_and(|inner| exp_mentions_name(inner, target))
                || exp_mentions_name(mime_type, target)
        }
        Exp::Query(QueryMeta {
            query,
            body,
            initial,
            ..
        }) => {
            exp_mentions_name(query, target)
                || exp_mentions_name(body, target)
                || exp_mentions_name(initial, target)
        }
        Exp::Prim(_) | Exp::Rel(_) | Exp::Ffi(_, _) | Exp::None(_) | Exp::Con(_, _, None) => false,
    }
}

fn pat_mentions_name(pat: &LocPat, target: usize) -> bool {
    match &pat.node {
        Pat::Con(_, crate::monomorphized::PatCon::Var(n), inner) => {
            *n == target
                || inner
                    .as_ref()
                    .is_some_and(|inner| pat_mentions_name(inner, target))
        }
        Pat::Con(_, _, Some(inner)) | Pat::Some(_, inner) => pat_mentions_name(inner, target),
        Pat::Record(fields) => fields
            .iter()
            .any(|(_, inner, _)| pat_mentions_name(inner, target)),
        Pat::Var(_, _) | Pat::Prim(_) | Pat::Con(_, _, None) | Pat::None(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn string_typ() -> LocTyp {
        Located::dummy(Typ::Ffi("Basis".into(), "string".into()))
    }

    fn unit_typ() -> LocTyp {
        Located::dummy(Typ::Record(vec![]))
    }

    fn rel(n: usize) -> LocExp {
        Located::dummy(Exp::Rel(n))
    }

    fn abs(x: &str, dom: LocTyp, ran: LocTyp, body: LocExp) -> LocExp {
        Located::dummy(Exp::Abs(x.into(), dom, ran, Box::new(body)))
    }

    #[test]
    fn hoists_closed_record_lambda() {
        let fun_typ = Located::dummy(Typ::Fun(Box::new(string_typ()), Box::new(string_typ())));
        let lambda = abs("x", string_typ(), string_typ(), rel(0));
        let value = Located::dummy(Exp::Record(vec![("f".into(), lambda, fun_typ.clone())]));
        let file = (
            vec![Located::dummy(Decl::Val(
                "holder".into(),
                1,
                Located::dummy(Typ::Record(vec![("f".into(), fun_typ.clone())])),
                value,
                String::new(),
            ))],
            vec![],
        );

        let out = hoist_closed_functions(file);
        assert_eq!(out.0.len(), 2);
        assert!(matches!(&out.0[0].node, Decl::Val(name, _, _, _, _) if name.starts_with("lam_")));
        match &out.0[1].node {
            Decl::Val(_, _, _, body, _) => match &body.node {
                Exp::Record(fields) => assert!(matches!(fields[0].1.node, Exp::Named(_))),
                other => panic!("expected record body, got {other:?}"),
            },
            other => panic!("expected value declaration, got {other:?}"),
        }
    }

    #[test]
    fn leaves_open_lambda_in_place() {
        let fun_typ = Located::dummy(Typ::Fun(Box::new(string_typ()), Box::new(string_typ())));
        let lambda = abs("x", string_typ(), string_typ(), rel(1));
        let body = Located::dummy(Exp::Let(
            "captured".into(),
            string_typ(),
            Box::new(Located::dummy(Exp::Prim(crate::primitives::Prim::String(
                crate::primitives::StringMode::Normal,
                "v".into(),
            )))),
            Box::new(lambda),
        ));
        let file = (
            vec![Located::dummy(Decl::Val(
                "holder".into(),
                1,
                fun_typ,
                body,
                String::new(),
            ))],
            vec![],
        );

        let out = hoist_closed_functions(file);
        assert_eq!(out.0.len(), 1);
        match &out.0[0].node {
            Decl::Val(_, _, _, body, _) => match &body.node {
                Exp::Let(_, _, _, inner) => assert!(matches!(inner.node, Exp::Abs(_, _, _, _))),
                other => panic!("expected let body, got {other:?}"),
            },
            other => panic!("expected value declaration, got {other:?}"),
        }
    }

    #[test]
    fn keeps_unit_thunks_for_cjr_forcing() {
        let thunk = abs("_", unit_typ(), string_typ(), rel(0));
        let file = (
            vec![Located::dummy(Decl::Val(
                "holder".into(),
                1,
                Located::dummy(Typ::Transaction(Box::new(string_typ()))),
                thunk,
                String::new(),
            ))],
            vec![],
        );

        let out = hoist_closed_functions(file);
        assert_eq!(out.0.len(), 1);
        match &out.0[0].node {
            Decl::Val(_, _, _, body, _) => assert!(matches!(body.node, Exp::Abs(_, _, _, _))),
            other => panic!("expected value declaration, got {other:?}"),
        }
    }

    #[test]
    fn hoisted_helpers_inside_script_decls_keep_script_marker() {
        let fun_typ = Located::dummy(Typ::Fun(Box::new(string_typ()), Box::new(string_typ())));
        let lambda = abs("x", string_typ(), string_typ(), rel(0));
        let value = Located::dummy(Exp::Record(vec![("f".into(), lambda, fun_typ.clone())]));
        let file = (
            vec![Located::dummy(Decl::Val(
                "script_holder".into(),
                1,
                Located::dummy(Typ::Record(vec![("f".into(), fun_typ.clone())])),
                value,
                "<script>".into(),
            ))],
            vec![],
        );

        let out = hoist_closed_functions(file);
        assert_eq!(out.0.len(), 2);
        match &out.0[0].node {
            Decl::Val(name, _, _, _, sql_name) => {
                assert!(name.starts_with("lam_"));
                assert_eq!(sql_name, "<script>");
            }
            other => panic!("expected hoisted helper, got {other:?}"),
        }
    }

    #[test]
    fn hoisted_helpers_do_not_reuse_constructor_ids() {
        let constructor_id = 99;
        let fun_typ = Located::dummy(Typ::Fun(Box::new(string_typ()), Box::new(string_typ())));
        let lambda = abs("x", string_typ(), string_typ(), rel(0));
        let file = (
            vec![
                Located::dummy(Decl::Datatype(vec![crate::monomorphized::DatatypeDecl {
                    name: "dt".into(),
                    id: 50,
                    constrs: vec![("Mk".into(), constructor_id, None)],
                }])),
                Located::dummy(Decl::Val(
                    "holder".into(),
                    1,
                    fun_typ,
                    lambda,
                    String::new(),
                )),
            ],
            vec![],
        );

        let out = hoist_closed_functions(file);
        match &out.0[0].node {
            Decl::Datatype(_) => {}
            other => panic!("expected datatype declaration first, got {other:?}"),
        }
        match &out.0[1].node {
            Decl::Val(name, n, _, _, _) => {
                assert!(name.starts_with("lam_"));
                assert!(*n > constructor_id);
            }
            other => panic!("expected hoisted helper, got {other:?}"),
        }
    }

    #[test]
    fn hoisted_helpers_do_not_reuse_export_info_ids() {
        let fun_typ = Located::dummy(Typ::Fun(Box::new(string_typ()), Box::new(string_typ())));
        let lambda = abs("x", string_typ(), string_typ(), rel(0));
        let file = (
            vec![Located::dummy(Decl::Val(
                "holder".into(),
                1,
                fun_typ,
                lambda,
                String::new(),
            ))],
            vec![(41, Sidedness::ServerOnly, DbMode::AnyDb)],
        );

        let out = hoist_closed_functions(file);
        match &out.0[0].node {
            Decl::Val(name, n, _, _, _) => {
                assert!(name.starts_with("lam_"));
                assert!(*n > 41);
            }
            other => panic!("expected hoisted helper, got {other:?}"),
        }
    }

    #[test]
    fn hoisted_helper_ids_avoid_named_refs_in_body() {
        let mut pass = HoistClosedFunctions { next_name: 7 };
        let mut helpers = Vec::new();
        let lambda = abs(
            "x",
            string_typ(),
            string_typ(),
            Located::dummy(Exp::Named(7)),
        );

        let rewritten = pass.rewrite_exp(lambda, &mut helpers, None);
        assert!(matches!(rewritten.node, Exp::Named(8)));
        match &helpers[0].node {
            Decl::Val(name, n, _, _, _) => {
                assert_eq!(name, "lam_8");
                assert_eq!(*n, 8);
            }
            other => panic!("expected hoisted helper, got {other:?}"),
        }
    }

    #[test]
    fn keeps_abs_when_it_is_the_root_field_receiver() {
        let record_t = Located::dummy(Typ::Record(vec![("A".into(), string_typ())]));
        let receiver = abs(
            "_",
            unit_typ(),
            record_t,
            Located::dummy(Exp::Record(vec![(
                "A".into(),
                Located::dummy(Exp::Prim(crate::primitives::Prim::String(
                    crate::primitives::StringMode::Normal,
                    "ok".into(),
                ))),
                string_typ(),
            )])),
        );
        let body = Located::dummy(Exp::Field(Box::new(receiver), "A".into()));
        let file = (
            vec![Located::dummy(Decl::Val(
                "holder".into(),
                1,
                string_typ(),
                body,
                String::new(),
            ))],
            vec![],
        );

        let out = hoist_closed_functions(file);
        assert_eq!(out.0.len(), 1);
        match &out.0[0].node {
            Decl::Val(_, _, _, body, _) => match &body.node {
                Exp::Field(inner, field) => {
                    assert_eq!(field, "A");
                    assert!(matches!(inner.node, Exp::Abs(_, _, _, _)));
                }
                other => panic!("expected field body, got {other:?}"),
            },
            other => panic!("expected value declaration, got {other:?}"),
        }
    }
}
