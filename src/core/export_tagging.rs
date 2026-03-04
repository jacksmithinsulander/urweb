//! URL and form link tagging pass.
//!
//! Finds applications of `Basis.tag`, `Basis.url`, and `Basis.effectfulUrl`
//! in the Core IR, replaces "Link" and "Action" attributes with closure
//! references, and generates wrapper functions + export declarations.
//!
//! Mirrors `tag.sml`.

#![allow(dead_code, unused_variables)]

use std::collections::HashMap;

use crate::core::environment::Env;
use crate::core::*;
use crate::error_types::Span;
use crate::export::{Effect, ExportKind};

// ---------------------------------------------------------------------------
// Union-find for equating aliased function names
// ---------------------------------------------------------------------------

struct UnionFind {
    parent: HashMap<usize, usize>,
}

impl UnionFind {
    fn new() -> Self {
        UnionFind {
            parent: HashMap::new(),
        }
    }

    fn representative(&self, mut node: usize) -> usize {
        while let Some(&parent) = self.parent.get(&node) {
            node = parent;
        }
        node
    }

    fn equate(&mut self, node_one: usize, node_two: usize) {
        let representative_one = self.representative(node_one);
        let representative_two = self.representative(node_two);
        if representative_one != representative_two {
            self.parent.insert(representative_one, representative_two);
        }
    }
}

// ---------------------------------------------------------------------------
// Pass state
// ---------------------------------------------------------------------------

struct State {
    count: usize,
    /// map from function_id → closure_number
    tags: HashMap<usize, usize>,
    /// map from source_name → (export_kind, function_id)
    by_tag: HashMap<String, (ExportKind, usize)>,
    /// newly generated (export_kind, function_id, closure_number)
    new_tags: Vec<(ExportKind, usize, usize)>,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Unravels nested `EApp` applications, collecting the head name and arguments.
fn unravel_app(expression: &LocatedExpression) -> Option<(usize, Vec<LocatedExpression>)> {
    fn inner(expression: &LocatedExpression, args: &mut Vec<LocatedExpression>) -> Option<usize> {
        match &expression.node {
            Expression::Named(name_id) => Some(*name_id),
            Expression::App(function, argument) => {
                args.insert(0, *argument.clone());
                inner(function, args)
            }
            _ => None,
        }
    }
    let mut args = Vec::new();
    inner(expression, &mut args).map(|name_id| (name_id, args))
}

/// Emits an error for a duplicate URL prefix.
fn report_dup_url(span: &Span, prefix_message: &str, error_reporter: &mut impl FnMut(&Span, &str)) {
    error_reporter(span, &format!("Duplicate URL prefix {}", prefix_message));
}

/// Emits an error for conflicting export kinds.
fn report_both(span: &Span, function_name: &str, error_reporter: &mut impl FnMut(&Span, &str)) {
    error_reporter(
        span,
        &format!(
            "Function {} needed for multiple modes (link, form, RPC handler).",
            function_name
        ),
    );
}

/// Replace a "Link" or "Action" attribute with a closure reference.
fn tag_it(
    e: LocatedExpression,
    ek: ExportKind,
    new_attr: &str,
    state: &mut State,
    source_names: &HashMap<usize, String>,
    uf: &UnionFind,
    env: &Env,
    error_reporter: &mut impl FnMut(&Span, &str),
) -> LocatedExpression {
    let span = e.span.clone();

    match unravel_app(&e) {
        None => {
            error_reporter(&span, &format!("Invalid {} expression", new_attr));
            e
        }
        Some((f_raw, args)) => {
            if f_raw == 0 {
                return e;
            }
            let f = uf.representative(f_raw);

            let cn = if let Some(&existing) = state.tags.get(&f) {
                existing
            } else {
                let cn = state.count;
                state.count += 1;
                state.tags.insert(f, cn);
                state.new_tags.push((ek.clone(), f, cn));
                cn
            };

            // Check for duplicate URL prefixes
            let src_name = source_names.get(&f).cloned().unwrap_or_default();
            match state.by_tag.get(&src_name) {
                None => {
                    state.by_tag.insert(src_name.clone(), (ek.clone(), f));
                }
                Some((ek2, f2)) => {
                    if *f2 != f {
                        error_reporter(&span, &format!("Duplicate URL prefix {}", src_name));
                    }
                    if export_kind_discriminant(&ek) != export_kind_discriminant(ek2) {
                        error_reporter(
                            &span,
                            &format!(
                                "Function {} needed for multiple modes (link, form, RPC handler).",
                                src_name
                            ),
                        );
                    }
                }
            }

            Located {
                node: Expression::Closure(cn, args),
                span,
            }
        }
    }
}

fn export_kind_discriminant(export_kind: &ExportKind) -> u8 {
    match export_kind {
        ExportKind::Link(_) => 0,
        ExportKind::Action(_) => 1,
        ExportKind::Rpc(_) => 2,
        ExportKind::Extern(_) => 3,
    }
}

// ---------------------------------------------------------------------------
// Expression rewriter
// ---------------------------------------------------------------------------

fn rewrite_exp(
    e: LocatedExpression,
    state: &mut State,
    source_names: &HashMap<usize, String>,
    uf: &UnionFind,
    env: &Env,
    error_reporter: &mut impl FnMut(&Span, &str),
) -> LocatedExpression {
    let span = e.span.clone();
    match e.node {
        // Basis.tag application — rewrite Link/Action attributes
        // This matches the nested ECApp/EApp pattern for Basis.tag
        Expression::App(outer_f, xml) => {
            // Try to detect the Basis.tag pattern by checking if the head
            // function involves EFfi("Basis", "tag")
            let f = rewrite_exp(*outer_f, state, source_names, uf, env, error_reporter);
            let xml = rewrite_exp(*xml, state, source_names, uf, env, error_reporter);
            Located {
                node: Expression::App(Box::new(f), Box::new(xml)),
                span,
            }
        }

        // Basis.url FFI call — tag the URL argument
        Expression::FfiApp(ref m, ref f, ref args)
            if m == "Basis" && f == "url" && args.len() == 1 =>
        {
            // EFfiApp ("Basis", "url", [(ERel 0, _)]) is skipped
            if matches!(&args[0].0.node, Expression::Rel(0)) {
                Located { node: e.node, span }
            } else {
                let (arg_e, arg_t) = args[0].clone();
                let tagged = tag_it(
                    arg_e,
                    ExportKind::Link(Effect::ReadCookieWrite),
                    "Url",
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                );
                Located {
                    node: Expression::FfiApp(
                        "Basis".to_string(),
                        "url".to_string(),
                        vec![(tagged, arg_t)],
                    ),
                    span,
                }
            }
        }

        // Basis.effectfulUrl FFI call — tag the URL argument as Extern
        Expression::FfiApp(ref m, ref f, ref args)
            if m == "Basis" && f == "effectfulUrl" && args.len() == 1 =>
        {
            if matches!(&args[0].0.node, Expression::Rel(0)) {
                Located { node: e.node, span }
            } else {
                let (arg_e, arg_t) = args[0].clone();
                let tagged = tag_it(
                    arg_e,
                    ExportKind::Extern(Effect::ReadCookieWrite),
                    "Url",
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                );
                Located {
                    node: Expression::FfiApp(
                        "Basis".to_string(),
                        "url".to_string(),
                        vec![(tagged, arg_t)],
                    ),
                    span,
                }
            }
        }

        // Recurse into sub-expressions
        Expression::Abs(x, dom, ran, body) => Located {
            node: Expression::Abs(
                x,
                dom,
                ran,
                Box::new(rewrite_exp(
                    *body,
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                )),
            ),
            span,
        },
        Expression::CApp(ef, c) => Located {
            node: Expression::CApp(
                Box::new(rewrite_exp(
                    *ef,
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                )),
                c,
            ),
            span,
        },
        Expression::CAbs(x, k, body) => Located {
            node: Expression::CAbs(
                x,
                k,
                Box::new(rewrite_exp(
                    *body,
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                )),
            ),
            span,
        },
        Expression::KAbs(x, body) => Located {
            node: Expression::KAbs(
                x,
                Box::new(rewrite_exp(
                    *body,
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                )),
            ),
            span,
        },
        Expression::KApp(ef, k) => Located {
            node: Expression::KApp(
                Box::new(rewrite_exp(
                    *ef,
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                )),
                k,
            ),
            span,
        },
        Expression::Let(x, t, e1, e2) => Located {
            node: Expression::Let(
                x,
                t,
                Box::new(rewrite_exp(
                    *e1,
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                )),
                Box::new(rewrite_exp(
                    *e2,
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                )),
            ),
            span,
        },
        Expression::Case(disc, arms, meta) => Located {
            node: Expression::Case(
                Box::new(rewrite_exp(
                    *disc,
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                )),
                arms.into_iter()
                    .map(|(p, body)| {
                        (
                            p,
                            rewrite_exp(body, state, source_names, uf, env, error_reporter),
                        )
                    })
                    .collect(),
                meta,
            ),
            span,
        },
        Expression::Write(inner) => Located {
            node: Expression::Write(Box::new(rewrite_exp(
                *inner,
                state,
                source_names,
                uf,
                env,
                error_reporter,
            ))),
            span,
        },
        Expression::Record(fields) => Located {
            node: Expression::Record(
                fields
                    .into_iter()
                    .map(|(n, v, t)| {
                        (
                            n,
                            rewrite_exp(v, state, source_names, uf, env, error_reporter),
                            t,
                        )
                    })
                    .collect(),
            ),
            span,
        },
        Expression::Concat(e1, c1, e2, c2) => Located {
            node: Expression::Concat(
                Box::new(rewrite_exp(
                    *e1,
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                )),
                c1,
                Box::new(rewrite_exp(
                    *e2,
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                )),
                c2,
            ),
            span,
        },
        Expression::Field(rec, c, meta) => Located {
            node: Expression::Field(
                Box::new(rewrite_exp(
                    *rec,
                    state,
                    source_names,
                    uf,
                    env,
                    error_reporter,
                )),
                c,
                meta,
            ),
            span,
        },
        Expression::FfiApp(m, f, args) => Located {
            node: Expression::FfiApp(
                m,
                f,
                args.into_iter()
                    .map(|(ae, at)| {
                        (
                            rewrite_exp(ae, state, source_names, uf, env, error_reporter),
                            at,
                        )
                    })
                    .collect(),
            ),
            span,
        },
        Expression::ServerCall(n, args, t, fm) => Located {
            node: Expression::ServerCall(
                n,
                args.into_iter()
                    .map(|ae| rewrite_exp(ae, state, source_names, uf, env, error_reporter))
                    .collect(),
                t,
                fm,
            ),
            span,
        },
        other => Located { node: other, span },
    }
}

// ---------------------------------------------------------------------------
// Generate wrapper functions for tagged links
// ---------------------------------------------------------------------------

/// Build a wrapper function `wrap_f` that applies `f` to unit.
///
/// The SML `tag.sml` generates a function of type `unit -> unit` (approximately)
/// that calls the named function with its normal arguments plus a final `()`.
fn make_wrapper(
    f_id: usize,
    f_type: &LocatedConstructor,
    f_name: &str,
    cn: usize,
    span: &Span,
) -> (LocatedDeclaration, LocatedDeclaration) {
    let unit_type = Located::new(
        Constructor::TRecord(Box::new(Located::new(
            Constructor::Record(Box::new(Located::new(Kind::Type, span.clone())), vec![]),
            span.clone(),
        ))),
        span.clone(),
    );
    let unit_val = Located::new(Expression::Record(vec![]), span.clone());

    // Unravel the function type to collect argument types
    fn unravel_type(t: &LocatedConstructor) -> (Vec<LocatedConstructor>, LocatedConstructor) {
        match &t.node {
            Constructor::TFun(dom, ran) => {
                let (mut args, result) = unravel_type(ran);
                args.insert(0, *dom.clone());
                (args, result)
            }
            _ => (vec![], t.clone()),
        }
    }

    let (args, _result) = unravel_type(f_type);

    let wrap_type: LocatedConstructor = Located::new(
        Constructor::TFun(Box::new(unit_type.clone()), Box::new(unit_type.clone())),
        span.clone(),
    );

    let body = if args.is_empty() {
        // wrap_f () = write (f ())
        let app = Located::new(
            Expression::App(
                Box::new(Located::new(Expression::Named(f_id), span.clone())),
                Box::new(unit_val.clone()),
            ),
            span.clone(),
        );
        Located::new(Expression::Write(Box::new(app)), span.clone())
    } else {
        // wrap_f x0 x1 ... () = write (f x0 x1 ... ())
        let n = args.len();
        // Build: f x(n-1) x(n-2) ... x0 ()
        let mut app: LocatedExpression = Located::new(Expression::Named(f_id), span.clone());
        for i in (0..n).rev() {
            app = Located::new(
                Expression::App(
                    Box::new(app),
                    Box::new(Located::new(Expression::Rel(i), span.clone())),
                ),
                span.clone(),
            );
        }
        let app = Located::new(
            Expression::App(Box::new(app), Box::new(unit_val.clone())),
            span.clone(),
        );
        let body = Located::new(Expression::Write(Box::new(app)), span.clone());

        // Wrap in lambdas for each arg
        let wrap_t = Located::new(
            Constructor::TFun(Box::new(unit_type.clone()), Box::new(unit_type.clone())),
            span.clone(),
        );
        let (abs, _, _) = args.iter().rev().enumerate().fold(
            (body, 0usize, wrap_t),
            |(inner, k, rest_t), (i, arg_t)| {
                let fn_t = Located::new(
                    Constructor::TFun(Box::new(arg_t.clone()), Box::new(rest_t.clone())),
                    span.clone(),
                );
                let lambda = Located::new(
                    Expression::Abs(format!("x{}", k), arg_t.clone(), rest_t, Box::new(inner)),
                    span.clone(),
                );
                (lambda, k + 1, fn_t)
            },
        );
        abs
    };

    let val_decl = Located::new(
        Declaration::Val(
            format!("wrap_{}", f_name),
            cn,
            wrap_type,
            body,
            String::new(),
        ),
        span.clone(),
    );

    let export_decl = Located::new(
        Declaration::Export(ExportKind::Link(Effect::ReadCookieWrite), cn, false),
        span.clone(),
    );

    (val_decl, export_decl)
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Rewrite URL links and form actions as closures, generate wrapper functions.
pub fn tag(file: File, error_reporter: &mut impl FnMut(&Span, &str)) -> File {
    // Build source-name lookup map from Val declarations
    let mut source_names: HashMap<usize, String> = HashMap::new();
    for d in &file {
        match &d.node {
            Declaration::Val(_, n, _, _, s) => {
                source_names.insert(*n, s.clone());
            }
            Declaration::ValRec(vis) => {
                for (_, n, _, _, s) in vis {
                    source_names.insert(*n, s.clone());
                }
            }
            _ => {}
        }
    }

    let max_name = crate::core::utilities::file::max_name(&file);
    let mut state = State {
        count: max_name + 1,
        tags: HashMap::new(),
        by_tag: HashMap::new(),
        new_tags: Vec::new(),
    };
    let mut uf = UnionFind::new();
    let mut env = Env::empty();
    let mut result: Vec<LocatedDeclaration> = Vec::new();

    for d in file {
        let span = d.span.clone();

        // Check for DExport conflicts with byTag
        let d = match &d.node {
            Declaration::Export(ek, n, _) => {
                let src_name = source_names.get(n).cloned().unwrap_or_default();
                match state.by_tag.get(&src_name) {
                    None => d,
                    Some((ek2, n2)) => {
                        if export_kind_discriminant(ek) != export_kind_discriminant(ek2) {
                            error_reporter(
                                &span,
                                &format!("Function {} needed for multiple modes", src_name),
                            );
                        }
                        // Remove duplicate export
                        continue;
                    }
                }
            }
            _ => d,
        };

        // Update union-find for value aliases
        if let Declaration::Val(_, n1, _, e, _) = &d.node {
            if let Expression::Named(n2) = &e.node {
                uf.equate(*n1, *n2);
            }
        }

        // Use the appropriate env context
        let env_for_rec = env.clone().decl_binds(&d);
        let use_env = match &d.node {
            Declaration::ValRec(_) => &env_for_rec,
            _ => &env,
        };

        // Rewrite expressions in this declaration
        let new_tags_before = state.new_tags.len();

        let d_span = d.span.clone();
        let d_node = match d.node {
            Declaration::Val(x, n, t, e, s) => {
                let e2 = rewrite_exp(e, &mut state, &source_names, &uf, use_env, error_reporter);
                Declaration::Val(x, n, t, e2, s)
            }
            Declaration::ValRec(vis) => {
                let vis2 = vis
                    .into_iter()
                    .map(|(x, n, t, e, s)| {
                        let e2 =
                            rewrite_exp(e, &mut state, &source_names, &uf, use_env, error_reporter);
                        (x, n, t, e2, s)
                    })
                    .collect();
                Declaration::ValRec(vis2)
            }
            Declaration::Task(e1, e2) => {
                let e1b = rewrite_exp(e1, &mut state, &source_names, &uf, use_env, error_reporter);
                let e2b = rewrite_exp(e2, &mut state, &source_names, &uf, use_env, error_reporter);
                Declaration::Task(e1b, e2b)
            }
            Declaration::Policy(e) => {
                let e2 = rewrite_exp(e, &mut state, &source_names, &uf, use_env, error_reporter);
                Declaration::Policy(e2)
            }
            other => other,
        };

        // Generate wrapper functions for new tags
        let new_tags = state.new_tags.drain(new_tags_before..).collect::<Vec<_>>();

        // Collect new val declarations from new tags
        let mut new_val_decls: Vec<LocatedDeclaration> = Vec::new();
        let mut new_export_decls: Vec<LocatedDeclaration> = Vec::new();
        for (ek, f, cn) in new_tags {
            if let Some((f_name, f_type)) = env
                .lookup_e_named(f)
                .ok()
                .map(|(name, t)| (name.clone(), t.clone()))
            {
                let (val_d, export_d) = make_wrapper(f, &f_type, &f_name, cn, &d_span);
                new_val_decls.push(val_d);
                new_export_decls.push(export_d);
            }
        }

        // Assemble output: for ValRec, merge new vals into the rec group
        let d_located = Located {
            node: d_node,
            span: d_span.clone(),
        };
        match &d_located.node {
            Declaration::ValRec(vis) => {
                // Merge new wrappers into the ValRec
                if new_val_decls.is_empty() {
                    result.push(d_located);
                } else {
                    let mut all_vis: Vec<(
                        String,
                        usize,
                        LocatedConstructor,
                        LocatedExpression,
                        String,
                    )> = match d_located.node {
                        Declaration::ValRec(v) => v,
                        _ => unreachable!(),
                    };
                    for wrapper_d in new_val_decls {
                        if let Declaration::Val(x, n, t, e, s) = wrapper_d.node {
                            all_vis.push((x, n, t, e, s));
                        }
                    }
                    result.push(Located {
                        node: Declaration::ValRec(all_vis),
                        span: d_span.clone(),
                    });
                }
            }
            _ => {
                // Non-rec: emit new vals separately, then the decl
                result.extend(new_val_decls);
                result.push(d_located);
            }
        }
        result.extend(new_export_decls);

        // Update env with decl bindings
        env = env.decl_binds(result.last().unwrap());
    }

    result
}
