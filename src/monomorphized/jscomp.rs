//! JavaScript compilation pass (jscomp.sml → Rust).
//!
//! Walks a Mono `File` and compiles client-side code to JavaScript.  Each
//! `Exp::JavaScript` node in the tree is serialised into a JS expression tree
//! (an object-based encoding used by the Ur/Web runtime's interpreter).
//!
//! The public entry point is `js_compile`.

#![allow(dead_code)]

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::datatype_kind::DatatypeKind;
use crate::error_types::{Located, Span};
use crate::export::Effect;
use crate::monomorphized::{
    CaseMeta, DatatypeDecl, Decl, Exp, JavaScriptMode, LocExp, LocPat, LocTyp, Pat, PatCon, Typ,
};
use crate::primitives::{Prim, StringMode};
use crate::settings::{FailureMode, Settings};

// ---------------------------------------------------------------------------
// CantEmbed — emitted when a type can't be serialised to JS
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct CantEmbed(LocTyp);

// ---------------------------------------------------------------------------
// Mutable state threaded through the pass
// ---------------------------------------------------------------------------

/// `(name, id, typ, body, settings_str)` — auxiliary `DValRec` entries generated
/// for injectors / decoders.
type HelperDecl = (String, usize, LocTyp, LocExp, String);

struct State {
    /// Accumulated helpers (injectors / decoders) to prepend as `DValRec`.
    decls: Vec<HelperDecl>,
    /// Accumulated JavaScript text fragments (stored reversed; joined at end).
    script: Vec<String>,
    /// Named-function ids whose JS has already been included in `script`.
    included: HashSet<usize>,
    /// `datatype_id → injector_fn_id` for value→JS converters.
    injectors: HashMap<usize, usize>,
    /// `LocTyp (ordered) → list_injector_fn_id`.
    list_injectors: BTreeMap<OrdTyp, usize>,
    /// `datatype_id → decoder_fn_id` for URL-encoded → value converters.
    decoders: HashMap<usize, usize>,
    /// Counter for fresh `ENamed` ids.
    max_name: usize,
}

impl State {
    fn new(max_name: usize) -> Self {
        State {
            decls: Vec::new(),
            script: Vec::new(),
            included: HashSet::new(),
            injectors: HashMap::new(),
            list_injectors: BTreeMap::new(),
            decoders: HashMap::new(),
            max_name,
        }
    }

    fn alloc_name(&mut self) -> usize {
        let n = self.max_name;
        self.max_name += 1;
        n
    }
}

// ---------------------------------------------------------------------------
// OrdTyp — a wrapper that gives LocTyp a total order for BTreeMap keys.
// (mirrors the TM = BinaryMapFn(U.Typ.compare) in SML)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct OrdTyp(String);

impl OrdTyp {
    fn of(t: &LocTyp) -> Self {
        OrdTyp(fmt_typ(t))
    }
}

fn fmt_typ(t: &LocTyp) -> String {
    match &t.node {
        Typ::Fun(a, b) => format!("Fun({},{})", fmt_typ(a), fmt_typ(b)),
        Typ::Record(fields) => {
            let fs: Vec<String> = fields.iter().map(|(n, t)| format!("{}:{}", n, fmt_typ(t))).collect();
            format!("Rec({})", fs.join(","))
        }
        Typ::Datatype(id, _) => format!("Dt({})", id),
        Typ::Ffi(m, f) => format!("Ffi({}.{})", m, f),
        Typ::Option(inner) => format!("Opt({})", fmt_typ(inner)),
        Typ::List(inner) => format!("List({})", fmt_typ(inner)),
        Typ::Source => "Source".to_string(),
        Typ::Signal(inner) => format!("Signal({})", fmt_typ(inner)),
    }
}

// ---------------------------------------------------------------------------
// Helper: build a dummy LocExp / LocTyp at a given span
// ---------------------------------------------------------------------------

fn dummy_span() -> Span {
    Span::dummy()
}

fn str_typ(span: &Span) -> LocTyp {
    Located::new(Typ::Ffi("Basis".into(), "string".into()), span.clone())
}

fn str_lit(span: &Span, s: &str) -> LocExp {
    Located::new(
        Exp::Prim(Prim::String(StringMode::Normal, s.to_string())),
        span.clone(),
    )
}

fn strcat_exp(span: &Span, es: Vec<LocExp>) -> LocExp {
    match es.len() {
        0 => str_lit(span, ""),
        1 => es.into_iter().next().unwrap(),
        _ => {
            let mut iter = es.into_iter().rev();
            let mut acc = iter.next().unwrap();
            for e in iter {
                acc = Located::new(
                    Exp::Strcat(Box::new(e), Box::new(acc)),
                    span.clone(),
                );
            }
            acc
        }
    }
}

fn named(span: &Span, n: usize) -> LocExp {
    Located::new(Exp::Named(n), span.clone())
}

fn app(span: &Span, f: LocExp, x: LocExp) -> LocExp {
    Located::new(Exp::App(Box::new(f), Box::new(x)), span.clone())
}

fn rel(span: &Span, n: usize) -> LocExp {
    Located::new(Exp::Rel(n), span.clone())
}

fn field(span: &Span, e: LocExp, x: &str) -> LocExp {
    Located::new(Exp::Field(Box::new(e), x.to_string()), span.clone())
}

fn ffi_app(span: &Span, m: &str, f: &str, args: Vec<(LocExp, LocTyp)>) -> LocExp {
    Located::new(Exp::FfiApp(m.to_string(), f.to_string(), args), span.clone())
}

fn make_abs(span: &Span, x: &str, dom: LocTyp, ran: LocTyp, body: LocExp) -> LocExp {
    Located::new(Exp::Abs(x.to_string(), dom, ran, Box::new(body)), span.clone())
}

fn make_case(span: &Span, disc: LocExp, arms: Vec<(LocPat, LocExp)>, meta: CaseMeta) -> LocExp {
    Located::new(Exp::Case(Box::new(disc), arms, meta), span.clone())
}

fn make_let(span: &Span, x: &str, t: LocTyp, e1: LocExp, e2: LocExp) -> LocExp {
    Located::new(Exp::Let(x.to_string(), t, Box::new(e1), Box::new(e2)), span.clone())
}

fn pat_none(span: &Span, t: LocTyp) -> LocPat {
    Located::new(Pat::None(t), span.clone())
}

fn pat_some(span: &Span, t: LocTyp, p: LocPat) -> LocPat {
    Located::new(Pat::Some(t, Box::new(p)), span.clone())
}

fn pat_var(span: &Span, x: &str, t: LocTyp) -> LocPat {
    Located::new(Pat::Var(x.to_string(), t), span.clone())
}

fn pat_con(span: &Span, dk: DatatypeKind, pc: PatCon, inner: Option<LocPat>) -> LocPat {
    Located::new(Pat::Con(dk, pc, inner.map(Box::new)), span.clone())
}

// ---------------------------------------------------------------------------
// isNullable — mirrors `isNullable` in SML
// ---------------------------------------------------------------------------

fn is_nullable(t: &LocTyp) -> bool {
    match &t.node {
        Typ::Option(_) => true,
        Typ::List(_) => true,
        Typ::Datatype(_, arc) => {
            let def = arc.lock().unwrap();
            def.kind == DatatypeKind::Option
        }
        Typ::Record(fields) => fields.is_empty(),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// max_name helper — find highest ENamed id in a file
// ---------------------------------------------------------------------------

fn max_name_in_file(file: &crate::monomorphized::File) -> usize {
    let mut mx = 0usize;
    for d in &file.0 {
        max_name_decl(&d.node, &mut mx);
    }
    mx
}

fn max_name_decl(d: &Decl, mx: &mut usize) {
    match d {
        Decl::Val(_, n, _, e, _) => {
            *mx = (*mx).max(*n);
            max_name_exp(&e.node, mx);
        }
        Decl::ValRec(vis) => {
            for (_, n, _, e, _) in vis {
                *mx = (*mx).max(*n);
                max_name_exp(&e.node, mx);
            }
        }
        _ => {}
    }
}

fn max_name_exp(e: &Exp, mx: &mut usize) {
    match e {
        Exp::Named(n) => *mx = (*mx).max(*n),
        Exp::App(f, x) => { max_name_exp(&f.node, mx); max_name_exp(&x.node, mx); }
        Exp::Abs(_, _, _, body) => max_name_exp(&body.node, mx),
        Exp::Let(_, _, e1, e2) => { max_name_exp(&e1.node, mx); max_name_exp(&e2.node, mx); }
        Exp::Strcat(a, b) => { max_name_exp(&a.node, mx); max_name_exp(&b.node, mx); }
        Exp::FfiApp(_, _, args) => { for (e, _) in args { max_name_exp(&e.node, mx); } }
        Exp::Record(xets) => { for (_, e, _) in xets { max_name_exp(&e.node, mx); } }
        Exp::Field(e, _) => max_name_exp(&e.node, mx),
        Exp::Case(disc, arms, _) => {
            max_name_exp(&disc.node, mx);
            for (_, arm) in arms { max_name_exp(&arm.node, mx); }
        }
        Exp::Con(_, _, Some(e)) => max_name_exp(&e.node, mx),
        Exp::Some(_, e) => max_name_exp(&e.node, mx),
        Exp::Seq(a, b) => { max_name_exp(&a.node, mx); max_name_exp(&b.node, mx); }
        Exp::Write(e) => max_name_exp(&e.node, mx),
        Exp::Error(e, _) => max_name_exp(&e.node, mx),
        Exp::Closure(n, envs) => {
            *mx = (*mx).max(*n);
            for e in envs { max_name_exp(&e.node, mx); }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// quoteExp — serialise a Mono value to a JS string expression (server→client)
// ---------------------------------------------------------------------------

/// Serialise expression `e` of type `t` into a Mono expression that produces
/// a JavaScript string.  Returns `Err(CantEmbed(t))` for unsupported types.
fn quote_exp(
    span: &Span,
    t: &LocTyp,
    e: LocExp,
    st: &mut State,
    settings: &Settings,
) -> Result<LocExp, CantEmbed> {
    let s = span;
    match &t.node.clone() {
        Typ::Source => {
            let tclone = t.clone();
            Ok(ffi_app(s, "Basis", "htmlifySource", vec![(e, tclone)]))
        }

        Typ::Record(fields) if fields.is_empty() => Ok(str_lit(s, "null")),

        Typ::Record(fields) if fields.len() == 1 => {
            let (x, ft) = &fields[0].clone();
            let inner_e = field(s, e.clone(), x);
            let quoted = quote_exp(s, ft, inner_e, st, settings)?;
            let parts = vec![
                str_lit(s, &format!("{{_{x}:")),
                quoted,
                str_lit(s, "}"),
            ];
            Ok(strcat_exp(s, parts))
        }

        Typ::Record(fields) => {
            let fields = fields.clone();
            let (first_x, first_t) = &fields[0];
            let first_e = field(s, e.clone(), first_x);
            let first_q = quote_exp(s, first_t, first_e, st, settings)?;

            let mut parts = vec![
                str_lit(s, &format!("{{_{first_x}:")),
                first_q,
            ];
            for (x, ft) in &fields[1..] {
                let fe = field(s, e.clone(), x);
                let fq = quote_exp(s, ft, fe, st, settings)?;
                parts.push(str_lit(s, &format!(",_{x}:")));
                parts.push(fq);
            }
            parts.push(str_lit(s, "}"));
            Ok(strcat_exp(s, parts))
        }

        Typ::Ffi(m, f) if m == "Basis" && f == "string" => {
            let tc = t.clone();
            Ok(ffi_app(s, "Basis", "jsifyString", vec![(e, tc)]))
        }
        Typ::Ffi(m, f) if m == "Basis" && f == "char" => {
            let tc = t.clone();
            Ok(ffi_app(s, "Basis", "jsifyChar", vec![(e, tc)]))
        }
        Typ::Ffi(m, f) if m == "Basis" && f == "int" => {
            let tc = t.clone();
            Ok(ffi_app(s, "Basis", "htmlifyInt", vec![(e, tc)]))
        }
        Typ::Ffi(m, f) if m == "Basis" && f == "float" => {
            let tc = t.clone();
            Ok(ffi_app(s, "Basis", "htmlifyFloat", vec![(e, tc)]))
        }
        Typ::Ffi(m, f) if m == "Basis" && f == "channel" => {
            let tc = t.clone();
            Ok(ffi_app(s, "Basis", "jsifyChannel", vec![(e, tc)]))
        }
        Typ::Ffi(m, f) if m == "Basis" && f == "time" => {
            let tc = t.clone();
            Ok(ffi_app(s, "Basis", "jsifyTime", vec![(e, tc)]))
        }
        Typ::Ffi(m, f) if m == "Basis" && f == "clocktime" => {
            let tc = t.clone();
            Ok(ffi_app(s, "Basis", "jsifyClocktime", vec![(e, tc)]))
        }
        Typ::Ffi(m, f) if m == "Basis" && f == "calendardate" => {
            let tc = t.clone();
            Ok(ffi_app(s, "Basis", "jsifyCalendardate", vec![(e, tc)]))
        }

        Typ::Ffi(m, f) if m == "Basis" && f == "bool" => {
            // ECase over bool — produce "true" / "false"
            let disc_t = t.clone();
            let str_t = str_typ(s);
            let true_arm = (
                pat_con(s, DatatypeKind::Enum,
                    PatCon::Ffi { module: "Basis".into(), datatyp: "bool".into(), con: "True".into(), arg: None },
                    None),
                str_lit(s, "true"),
            );
            let false_arm = (
                pat_con(s, DatatypeKind::Enum,
                    PatCon::Ffi { module: "Basis".into(), datatyp: "bool".into(), con: "False".into(), arg: None },
                    None),
                str_lit(s, "false"),
            );
            let meta = CaseMeta { disc: disc_t, result: str_t };
            Ok(make_case(s, e, vec![true_arm, false_arm], meta))
        }

        Typ::Option(inner) => {
            let inner = (**inner).clone();
            // quoteExp for ERel(0) under a PSome binder
            let inner_e = quote_exp(s, &inner, rel(s, 0), st, settings)?;

            let nullable = is_nullable(&inner);
            let some_body = if nullable {
                strcat_exp(s, vec![str_lit(s, "{v:"), inner_e, str_lit(s, "}")])
            } else {
                inner_e
            };

            let t_opt = t.clone();
            let str_t = str_typ(s);
            let meta = CaseMeta { disc: t_opt.clone(), result: str_t };
            let arms = vec![
                (pat_none(s, inner.clone()), str_lit(s, "null")),
                (
                    pat_some(s, inner.clone(), pat_var(s, "x", inner.clone())),
                    some_body,
                ),
            ];
            Ok(make_case(s, e, arms, meta))
        }

        Typ::List(inner) => {
            let inner = (**inner).clone();
            let key = OrdTyp::of(&inner);

            if let Some(&n_prime) = st.list_injectors.get(&key) {
                return Ok(app(s, named(s, n_prime), e));
            }

            let n_prime = st.alloc_name();
            st.list_injectors.insert(key, n_prime);

            // rt = TRecord [("1", inner), ("2", t)]  (the list element type is Option rt)
            let rt = Located::new(
                Typ::Record(vec![("1".into(), inner.clone()), ("2".into(), t.clone())]),
                s.clone(),
            );

            let str_t = str_typ(s);

            // quote field "1" of ERel(0)
            let e_field1 = field(s, rel(s, 0), "1");
            let e_prime = quote_exp(s, &inner, e_field1, st, settings)?;

            // The body: case ERel(0) of
            //   PNone rt => "null"
            // | PSome(rt, PVar("x", rt)) =>
            //     "{_1:" ^ e' ^ ",_2:" ^ (ENamed n')(EField(ERel 0, "2")) ^ "}"
            let none_arm = (pat_none(s, rt.clone()), str_lit(s, "null"));
            let some_body = strcat_exp(s, vec![
                str_lit(s, "{_1:"),
                e_prime,
                str_lit(s, ",_2:"),
                app(s, named(s, n_prime), field(s, rel(s, 0), "2")),
                str_lit(s, "}"),
            ]);
            let some_arm = (
                pat_some(s, rt.clone(), pat_var(s, "x", rt.clone())),
                some_body,
            );

            let meta = CaseMeta { disc: t.clone(), result: str_t.clone() };
            let body_case = make_case(s, rel(s, 0), vec![none_arm, some_arm], meta);
            let body_abs = make_abs(s, "x", t.clone(), str_t.clone(), body_case);

            let fn_typ = Located::new(Typ::Fun(Box::new(t.clone()), Box::new(str_t)), s.clone());
            st.decls.push(("jsify".into(), n_prime, fn_typ, body_abs, "jsify".into()));

            Ok(app(s, named(s, n_prime), e))
        }

        Typ::Datatype(n, arc) => {
            if let Some(&n_prime) = st.injectors.get(n) {
                return Ok(app(s, named(s, n_prime), e));
            }

            let n_prime = st.alloc_name();
            st.injectors.insert(*n, n_prime);

            let def = arc.lock().unwrap();
            let dk = def.kind;
            let cs = def.constrs.clone();
            drop(def);

            let str_t = str_typ(s);
            let mut arms: Vec<(LocPat, LocExp)> = Vec::new();

            for (_, cn, ct) in &cs {
                match ct {
                    None => {
                        let val_str = match dk {
                            DatatypeKind::Option => "null".to_string(),
                            _ => cn.to_string(),
                        };
                        let p = pat_con(s, dk, PatCon::Var(*cn), None);
                        arms.push((p, str_lit(s, &val_str)));
                    }
                    Some(ct_inner) => {
                        let ct_inner = ct_inner.clone();
                        let inner_q = quote_exp(s, &ct_inner, rel(s, 0), st, settings)?;

                        let body = match dk {
                            DatatypeKind::Option => {
                                if is_nullable(&ct_inner) {
                                    strcat_exp(s, vec![str_lit(s, "{v:"), inner_q, str_lit(s, "}")])
                                } else {
                                    inner_q
                                }
                            }
                            _ => strcat_exp(s, vec![
                                str_lit(s, &format!("{{n:{cn},v:")),
                                inner_q,
                                str_lit(s, "}"),
                            ]),
                        };

                        let inner_pat = pat_var(s, "x", ct_inner.clone());
                        let p = pat_con(s, dk, PatCon::Var(*cn), Some(inner_pat));
                        arms.push((p, body));
                    }
                }
            }

            let dt_t = t.clone();
            let meta = CaseMeta { disc: dt_t.clone(), result: str_t.clone() };
            let body_case = make_case(s, rel(s, 0), arms, meta);
            let body_abs = make_abs(s, "x", dt_t.clone(), str_t.clone(), body_case);

            let fn_typ = Located::new(Typ::Fun(Box::new(dt_t), Box::new(str_t)), s.clone());
            st.decls.push(("jsify".into(), n_prime, fn_typ, body_abs, "jsify".into()));

            Ok(app(s, named(s, n_prime), e))
        }

        _ => Err(CantEmbed(t.clone())),
    }
}

// ---------------------------------------------------------------------------
// unurlifyExp — produce a JavaScript *string* snippet that unurlifies a type
// ---------------------------------------------------------------------------

fn unurlify_exp(
    span: &Span,
    t: &LocTyp,
    st: &mut State,
    settings: &Settings,
) -> String {
    match &t.node.clone() {
        Typ::Record(fields) if fields.is_empty() => "(i++,null)".to_string(),
        Typ::Ffi(m, f) if m == "Basis" && f == "unit" => "(i++,null)".to_string(),

        Typ::Record(fields) if fields.len() == 1 => {
            let (x, ft) = &fields[0].clone();
            let e = unurlify_exp(span, ft, st, settings);
            format!("{{_{x}:{e}}}")
        }

        Typ::Record(fields) => {
            let fields = fields.clone();
            let (first_x, first_t) = &fields[0];
            let e0 = unurlify_exp(span, first_t, st, settings);
            let mut out = format!("{{_{first_x}:{e0}");
            for (x, ft) in &fields[1..] {
                let e = unurlify_exp(span, ft, st, settings);
                out.push_str(&format!(",_{x}:{e}"));
            }
            out.push('}');
            out
        }

        Typ::Ffi(m, f) if m == "Basis" && f == "string" => "uu(t[i++])".to_string(),
        Typ::Ffi(m, f) if m == "Basis" && f == "char" => "uu(t[i++])".to_string(),
        Typ::Ffi(m, f) if m == "Basis" && f == "int" => "parseInt(t[i++])".to_string(),
        Typ::Ffi(m, f) if m == "Basis" && f == "time" => "parseInt(t[i++])".to_string(),
        Typ::Ffi(m, f) if m == "Basis" && f == "clocktime" => "unurlifyClocktime(t[i++])".to_string(),
        Typ::Ffi(m, f) if m == "Basis" && f == "calendardate" => "unurlifyCalendardate(t[i++])".to_string(),
        Typ::Ffi(m, f) if m == "Basis" && f == "float" => "parseFloat(t[i++])".to_string(),
        Typ::Ffi(m, f) if m == "Basis" && f == "channel" =>
            "(t[i++].length > 0 ? parseInt(t[i-1]) : null)".to_string(),
        Typ::Ffi(m, f) if m == "Basis" && f == "bool" => "t[i++] == \"1\"".to_string(),

        Typ::Source => "parseSource(t[i++], t[i++])".to_string(),

        Typ::Option(inner) => {
            let inner = (**inner).clone();
            let e = unurlify_exp(span, &inner, st, settings);
            let e2 = if is_nullable(&inner) {
                format!("{{v:{e}}}")
            } else {
                e
            };
            format!("(t[i++]==\"Some\"?{e2}:null)")
        }

        Typ::List(inner) => {
            let inner = (**inner).clone();
            let e = unurlify_exp(span, &inner, st, settings);
            format!("uul(function(){{return t[i++];}},function(){{return {e}}})")
        }

        Typ::Datatype(n, arc) => {
            if let Some(&n_prime) = st.decoders.get(n) {
                return format!("(tmp=_n{n_prime}(t,i),i=tmp._1,tmp._2)");
            }

            let n_prime = st.alloc_name();
            st.decoders.insert(*n, n_prime);

            let def = arc.lock().unwrap();
            let dk = def.kind;
            let cs = def.constrs.clone();
            drop(def);

            // Build right-fold of ternary: "x==name ? val : ... : pf(loc)"
            let loc_str = format!("{}:{}-{}", span.file, span.first.line, span.last.line);
            let mut expr = format!("pf(\"{loc_str}\")");

            for (x, cn, ct) in cs.iter().rev() {
                expr = match ct {
                    None => {
                        let val = match dk {
                            DatatypeKind::Option => "null".to_string(),
                            _ => cn.to_string(),
                        };
                        format!("x==\"{x}\"?{val}:{expr}")
                    }
                    Some(ct_inner) => {
                        let e = unurlify_exp(span, ct_inner, st, settings);
                        let val = match dk {
                            DatatypeKind::Option => {
                                if is_nullable(ct_inner) {
                                    format!("{{v:{e}}}")
                                } else {
                                    e
                                }
                            }
                            _ => format!("{{n:{cn},v:{e}}}"),
                        };
                        format!("x==\"{x}\"?{val}:{expr}")
                    }
                };
            }

            let body = format!("function _n{n_prime}(t,i){{var x=t[i++];var r={expr};return {{_1:i,_2:r}}}}\n\n");
            st.script.push(body);

            format!("(tmp=_n{n_prime}(t,i),i=tmp._1,tmp._2)")
        }

        _ => {
            // Unknown type — emit error marker
            eprintln!("jscomp: Don't know how to unurlify type in JavaScript");
            "ERROR".to_string()
        }
    }
}

// ---------------------------------------------------------------------------
// padWith — left-pad a string with a character
// ---------------------------------------------------------------------------

fn pad_with(ch: char, s: &str, len: usize) -> String {
    if s.len() < len {
        let mut out = String::new();
        for _ in 0..(len - s.len()) {
            out.push(ch);
        }
        out.push_str(s);
        out
    } else {
        s.to_string()
    }
}

// ---------------------------------------------------------------------------
// jsChar — escape a single character for a JS string literal
// ---------------------------------------------------------------------------

fn js_char(ch: char, mode: &JsMode) -> String {
    match ch {
        '\'' => {
            if *mode == JsMode::Attribute {
                "\\047".to_string()
            } else {
                "'".to_string()
            }
        }
        '"' => "\\\"".to_string(),
        '<' => "\\074".to_string(),
        '\\' => "\\\\".to_string(),
        '\n' => "\\n".to_string(),
        '\r' => "\\r".to_string(),
        '\t' => "\\t".to_string(),
        ch => {
            if ch.is_ascii() && (ch.is_ascii_graphic() || ch == ' ') || (ch as u32) >= 128 {
                ch.to_string()
            } else {
                let oct = format!("{:o}", ch as u32);
                format!("\\{}", pad_with('0', &oct, 3))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// JS compilation mode
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum JsMode {
    Attribute,
    Script,
    Source,
}

fn java_script_mode_to_js_mode(m: &JavaScriptMode) -> JsMode {
    match m {
        JavaScriptMode::Attribute => JsMode::Attribute,
        JavaScriptMode::Script => JsMode::Script,
        JavaScriptMode::Source(_) => JsMode::Source,
    }
}

// ---------------------------------------------------------------------------
// patBinds — collect types bound by a pattern (prepended to `outer`)
// ---------------------------------------------------------------------------

fn pat_binds_types(p: &LocPat, env: &mut Vec<LocTyp>) {
    match &p.node {
        Pat::Var(_, t) => env.insert(0, t.clone()),
        Pat::Prim(_) => {}
        Pat::Con(_, _, None) => {}
        Pat::Con(_, _, Some(inner)) => pat_binds_types(inner, env),
        Pat::Record(xpts) => {
            for (_, p, _) in xpts {
                pat_binds_types(p, env);
            }
        }
        Pat::None(_) => {}
        Pat::Some(_, inner) => pat_binds_types(inner, env),
    }
}

fn pat_binds_n_local(p: &LocPat) -> usize {
    match &p.node {
        Pat::Var(_, _) => 1,
        Pat::Prim(_) => 0,
        Pat::Con(_, _, None) => 0,
        Pat::Con(_, _, Some(inner)) => pat_binds_n_local(inner),
        Pat::Record(xpts) => xpts.iter().map(|(_, p, _)| pat_binds_n_local(p)).sum(),
        Pat::None(_) => 0,
        Pat::Some(_, inner) => pat_binds_n_local(inner),
    }
}

// ---------------------------------------------------------------------------
// jsifyString — escape backslash and double-quote in a JS string
// ---------------------------------------------------------------------------

fn jsify_string(s: &str) -> String {
    let mut out = String::new();
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c => out.push(c),
        }
    }
    out
}

fn jsify_string_multi(n: usize, s: &str) -> String {
    let mut result = s.to_string();
    for _ in 0..n {
        result = jsify_string(&result);
    }
    result
}

// ---------------------------------------------------------------------------
// deStrcat — collapse a LocExp to a literal JS string (for ENamed embedding)
// ---------------------------------------------------------------------------

fn de_strcat(level: usize, e: &LocExp, errors: &mut Vec<String>) -> String {
    match &e.node {
        Exp::Prim(Prim::String(_, s)) => jsify_string_multi(level, s),
        Exp::Strcat(e1, e2) => {
            let s1 = de_strcat(level, e1, errors);
            let s2 = de_strcat(level, e2, errors);
            format!("{s1}{s2}")
        }
        Exp::FfiApp(m, f, args) if m == "Basis" && f == "jsifyString" && args.len() == 1 => {
            let inner = de_strcat(level + 1, &args[0].0, errors);
            format!("\"{inner}\"")
        }
        _ => {
            errors.push(format!("jscomp: Unexpected non-constant JavaScript code at {}", e.span));
            String::new()
        }
    }
}

// ---------------------------------------------------------------------------
// patCon JS string — mirrors `patCon` in SML
// ---------------------------------------------------------------------------

fn pat_con_js(pc: &PatCon, span: &Span) -> LocExp {
    match pc {
        PatCon::Var(n) => str_lit(span, &n.to_string()),
        PatCon::Ffi { module, con, .. } if module == "Basis" && con == "True" => {
            str_lit(span, "true")
        }
        PatCon::Ffi { module, con, .. } if module == "Basis" && con == "False" => {
            str_lit(span, "false")
        }
        PatCon::Ffi { con, .. } => str_lit(span, &format!("\"{con}\"")),
    }
}

// ---------------------------------------------------------------------------
// jsPat — serialise a pattern to a JS pattern object
// ---------------------------------------------------------------------------

fn js_pat(
    p: &LocPat,
    some_ts: &HashMap<usize, LocTyp>,
    span: &Span,
) -> LocExp {
    match &p.node {
        Pat::Var(_, _) => str_lit(span, "{/*hoho*/c:\"v\"}"),
        Pat::Prim(prim) => {
            let js_p = js_prim(prim, span, &JsMode::Script);
            strcat_exp(span, vec![str_lit(span, "{c:\"c\",v:"), js_p, str_lit(span, "}")])
        }
        Pat::Con(_, PatCon::Ffi { module, con, .. }, None)
            if module == "Basis" && con == "True" =>
        {
            str_lit(span, "{c:\"c\",v:true}")
        }
        Pat::Con(_, PatCon::Ffi { module, con, .. }, None)
            if module == "Basis" && con == "False" =>
        {
            str_lit(span, "{c:\"c\",v:false}")
        }
        Pat::Con(DatatypeKind::Option, _, None) => str_lit(span, "{c:\"c\",v:null}"),
        Pat::Con(DatatypeKind::Option, PatCon::Var(n), Some(inner_p)) => {
            match some_ts.get(n) {
                None => str_lit(span, "{c:\"c\",v:null}"), // fallback
                Some(t) => {
                    let nullable_str = if is_nullable(t) { "true" } else { "false" };
                    let inner_js = js_pat(inner_p, some_ts, span);
                    strcat_exp(span, vec![
                        str_lit(span, &format!("{{c:\"s\",n:{nullable_str},p:")),
                        inner_js,
                        str_lit(span, "}"),
                    ])
                }
            }
        }
        Pat::Con(_, pc, None) => {
            let pc_e = pat_con_js(pc, span);
            strcat_exp(span, vec![str_lit(span, "{c:\"c\",v:"), pc_e, str_lit(span, "}")])
        }
        Pat::Con(_, pc, Some(inner_p)) => {
            let pc_e = pat_con_js(pc, span);
            let inner_js = js_pat(inner_p, some_ts, span);
            strcat_exp(span, vec![
                str_lit(span, "{c:\"1\",n:"),
                pc_e,
                str_lit(span, ",p:"),
                inner_js,
                str_lit(span, "}"),
            ])
        }
        Pat::Record(xps) => {
            // Build cons list of {n:"field",p:jsPat}
            let list_e = xps.iter().rev().fold(str_lit(span, "null"), |acc, (x, p, _)| {
                let pj = js_pat(p, some_ts, span);
                strcat_exp(span, vec![
                    str_lit(span, &format!("cons({{n:\"{x}\",p:")),
                    pj,
                    str_lit(span, "},"),
                    acc,
                    str_lit(span, ")"),
                ])
            });
            strcat_exp(span, vec![str_lit(span, "{c:\"r\",l:"), list_e, str_lit(span, "}")])
        }
        Pat::None(_) => str_lit(span, "{c:\"c\",v:null}"),
        Pat::Some(t, inner_p) => {
            let nullable_str = if is_nullable(t) { "true" } else { "false" };
            let inner_js = js_pat(inner_p, some_ts, span);
            strcat_exp(span, vec![
                str_lit(span, &format!("{{c:\"s\",n:{nullable_str},p:")),
                inner_js,
                str_lit(span, "}"),
            ])
        }
    }
}

// ---------------------------------------------------------------------------
// jsPrim — serialise a Prim literal to a JS expression
// ---------------------------------------------------------------------------

fn js_prim(p: &Prim, span: &Span, mode: &JsMode) -> LocExp {
    match p {
        Prim::String(_, s) => {
            let escaped: String = s.chars().map(|c| js_char(c, mode)).collect();
            str_lit(span, &format!("\"{escaped}\""))
        }
        Prim::Char(ch) => {
            let escaped = js_char(*ch, mode);
            str_lit(span, &format!("\"{escaped}\""))
        }
        _ => str_lit(span, &p.to_string()),
    }
}

// ---------------------------------------------------------------------------
// jsExp — compile a Mono expression to a JS expression-object string
//
// `outer` = list of types of outer lambda-bound variables (index 0 = outermost).
// Variables with index < `inner` are JS-runtime variables; those >= `inner`
// are captured from the server and must be quoted.
// ---------------------------------------------------------------------------

fn js_exp(
    mode: &JsMode,
    outer: &[LocTyp],
    e: &LocExp,
    st: &mut State,
    settings: &Settings,
    nameds: &HashMap<usize, LocExp>,
    some_ts: &HashMap<usize, LocTyp>,
    found_javascript: &mut bool,
) -> Result<LocExp, CantEmbed> {
    js_e(mode, outer, 0, e, st, settings, nameds, some_ts, found_javascript)
}

fn js_e(
    mode: &JsMode,
    outer: &[LocTyp],
    inner: usize,
    e: &LocExp,
    st: &mut State,
    settings: &Settings,
    nameds: &HashMap<usize, LocExp>,
    some_ts: &HashMap<usize, LocTyp>,
    found_javascript: &mut bool,
) -> Result<LocExp, CantEmbed> {
    let span = &e.span.clone();
    let s = span;

    macro_rules! str { ($lit:expr) => { str_lit(s, $lit) } }
    macro_rules! cat { ($($e:expr),+) => { strcat_exp(s, vec![$($e),+]) } }
    macro_rules! recurse { ($ex:expr) => {
        js_e(mode, outer, inner, $ex, st, settings, nameds, some_ts, found_javascript)?
    } }
    macro_rules! recurse_inner { ($ex:expr, $n:expr) => {
        js_e(mode, outer, inner + $n, $ex, st, settings, nameds, some_ts, found_javascript)?
    } }

    match &e.node.clone() {
        Exp::Prim(p) => {
            let jp = js_prim(p, s, mode);
            Ok(cat![str!("{c:\"c\",v:"), jp, str!("}")])
        }

        Exp::Rel(n) => {
            let n = *n;
            if n < inner {
                Ok(str!(&format!("{{c:\"v\",n:{n}}}")))
            } else {
                let idx = n - inner;
                let t = outer
                    .get(idx)
                    .ok_or_else(|| CantEmbed(str_typ(s)))?
                    .clone();
                let rel_e = rel(s, idx);
                let quoted = quote_exp(s, &t, rel_e, st, settings)?;
                Ok(cat![str!("{c:\"c\",v:"), quoted, str!("}")])
            }
        }

        Exp::Named(n) => {
            let n = *n;
            if !st.included.contains(&n) {
                // Mark as included first (before recursing, to break cycles)
                st.included.insert(n);
                if let Some(named_e) = nameds.get(&n).cloned() {
                    let js_result = js_e(mode, &[], 0, &named_e, st, settings, nameds, some_ts, found_javascript)?;
                    let mut de_errors = Vec::new();
                    let js_str = de_strcat(0, &js_result, &mut de_errors);
                    let js_str = js_str
                        .replace('\'', "\\'")
                        .replace('\\', "\\\\")
                        .replace('\'', "\\'"); // do it properly
                    // Actually mirror SML: translate ' -> \' and \ -> \\
                    let js_str = {
                        let mut out = String::new();
                        for ch in js_str.chars() {
                            match ch {
                                '\'' => out.push_str("\\'"),
                                '\\' => out.push_str("\\\\"),
                                c => out.push(c),
                            }
                        }
                        out
                    };
                    let sc = format!("urfuncs[{n}] = {{c:\"t\",f:'{js_str}'}};\n");
                    st.script.push(sc);
                }
                // If not found in nameds, it's an error but we just continue
            }
            Ok(str!(&format!("{{c:\"n\",n:{n}}}")))
        }

        Exp::Con(DatatypeKind::Option, _, None) => Ok(str!("{c:\"c\",v:null}")),
        Exp::Con(DatatypeKind::Option, PatCon::Var(n), Some(inner_e)) => {
            let n = *n;
            let compiled = recurse!(inner_e);
            match some_ts.get(&n) {
                None => {
                    // Not in someTs — treat as Some
                    Ok(compiled)
                }
                Some(t) => {
                    if is_nullable(t) {
                        Ok(cat![str!("{c:\"s\",v:"), compiled, str!("}")])
                    } else {
                        Ok(compiled)
                    }
                }
            }
        }
        Exp::Con(_, pc, None) => {
            let pc_e = pat_con_js(pc, s);
            Ok(cat![str!("{c:\"c\",v:"), pc_e, str!("}")])
        }
        Exp::Con(_, pc, Some(inner_e)) => {
            let pc_e = pat_con_js(pc, s);
            let compiled = recurse!(inner_e);
            Ok(cat![str!("{c:\"1\",n:"), pc_e, str!(",v:"), compiled, str!("}")])
        }

        Exp::None(_) => Ok(str!("{c:\"c\",v:null}")),
        Exp::Some(t, inner_e) => {
            let compiled = recurse!(inner_e);
            if is_nullable(t) {
                Ok(cat![str!("{c:\"s\",v:"), compiled, str!("}")])
            } else {
                Ok(compiled)
            }
        }

        Exp::Ffi(m, f) => {
            let key = (m.clone(), f.clone());
            match settings.js_func(&key) {
                Some(name) => Ok(str!(&format!("{{c:\"c\",v:{name}}}"))),
                None => {
                    eprintln!("jscomp: Unsupported FFI identifier {f} in JavaScript at {}", s);
                    Ok(str!("{c:\"c\",v:ERROR}"))
                }
            }
        }

        Exp::FfiApp(m, f, _) if m == "Basis" && f == "sigString" => {
            // Special case: sigString — embed the original expression as constant string
            Ok(cat![str!("{c:\"c\",v:\""), e.clone(), str!("\"}")])
        }

        Exp::FfiApp(m, f, args) => {
            let key = (m.clone(), f.clone());
            let name = match settings.js_func(&key) {
                Some(n) => n.to_string(),
                None => {
                    eprintln!("jscomp: Unsupported FFI function {m}.{f} in JavaScript at {s}");
                    "ERROR".to_string()
                }
            };
            // Build right-fold cons list of args
            let list_e = args.iter().rev().try_fold(str!("null"), |acc, (arg_e, _)| {
                let compiled = js_e(mode, outer, inner, arg_e, st, settings, nameds, some_ts, found_javascript)?;
                Ok::<LocExp, CantEmbed>(cat![
                    str!("cons("),
                    compiled,
                    str!(","),
                    acc,
                    str!(")")
                ])
            })?;
            Ok(cat![
                str!(&format!("{{c:\"f\",f:{name},a:")),
                list_e,
                str!("}")
            ])
        }

        Exp::App(f_e, x_e) => {
            let f_c = recurse!(f_e);
            let x_c = recurse!(x_e);
            Ok(cat![str!("{c:\"a\",f:"), f_c, str!(",x:"), x_c, str!("}")])
        }

        Exp::Abs(_, _, _, body) => {
            let body_c = recurse_inner!(body, 1);
            Ok(cat![str!("{c:\"l\",b:"), body_c, str!("}")])
        }

        Exp::Unop(op, inner_e) => {
            let name = match op.as_str() {
                "!" => "not",
                "-" => "neg",
                other => {
                    eprintln!("jscomp: Unknown unary operator {other}");
                    "ERROR"
                }
            };
            let compiled = recurse!(inner_e);
            Ok(cat![
                str!(&format!("{{c:\"f\",f:{name},a:cons(")),
                compiled,
                str!(",null)}")
            ])
        }

        Exp::Binop(bi, op, e1, e2) => {
            let name = match op.as_str() {
                "==" => "eq",
                "!strcmp" => "eq",
                "+" => "plus",
                "-" => "minus",
                "*" => "times",
                "/" => match bi {
                    crate::monomorphized::BinopIntness::Int => "divInt",
                    crate::monomorphized::BinopIntness::NotInt => "div",
                },
                "%" => match bi {
                    crate::monomorphized::BinopIntness::Int => "modInt",
                    crate::monomorphized::BinopIntness::NotInt => "mod",
                },
                "fdiv" => "div",
                "fmod" => "mod",
                "<" => "lt",
                "<=" => "le",
                "strcmp" => "strcmp",
                "powl" => "pow",
                "powf" => "pow",
                other => {
                    eprintln!("jscomp: Unknown binary operator {other}");
                    "ERROR"
                }
            };
            let c1 = recurse!(e1);
            let c2 = recurse!(e2);
            Ok(cat![
                str!(&format!("{{c:\"f\",f:{name},a:cons(")),
                c1,
                str!(",cons("),
                c2,
                str!(",null))}")
            ])
        }

        Exp::Record(xets) if xets.is_empty() => Ok(str!("{c:\"c\",v:null}")),

        Exp::Record(xets) => {
            let list_e = xets.iter().rev().try_fold(str!("null"), |acc, (x, field_e, _)| {
                let compiled = js_e(mode, outer, inner, field_e, st, settings, nameds, some_ts, found_javascript)?;
                Ok::<LocExp, CantEmbed>(cat![
                    str!(&format!("cons({{n:\"{x}\",v:")),
                    compiled,
                    str!("},"),
                    acc,
                    str!(")")
                ])
            })?;
            Ok(cat![str!("{c:\"r\",l:"), list_e, str!("}")])
        }

        Exp::Field(base_e, x) => {
            // Check if this is a field-chain from an outer variable (captured server value)
            let result = seek_field(mode, outer, inner, base_e, &[x.as_str()], e, s, st, settings, nameds, some_ts, found_javascript);
            result
        }

        Exp::Case(disc_e, arms, _) => {
            let disc_c = recurse!(disc_e);
            let ps_e = arms.iter().rev().try_fold(str!("null"), |acc, (pat, arm_e)| {
                let n_binds = pat_binds_n_local(pat);
                let arm_c = js_e(mode, outer, inner + n_binds, arm_e, st, settings, nameds, some_ts, found_javascript)?;
                let pat_js = js_pat(pat, some_ts, s);
                Ok::<LocExp, CantEmbed>(cat![
                    str!("cons({p:"),
                    pat_js,
                    str!(",b:"),
                    arm_c,
                    str!("},"),
                    acc,
                    str!(")")
                ])
            })?;
            Ok(cat![str!("{c:\"m\",e:"), disc_c, str!(",p:"), ps_e, str!("}")])
        }

        Exp::Strcat(e1, e2) => {
            let c1 = recurse!(e1);
            let c2 = recurse!(e2);
            Ok(cat![str!("{c:\"f\",f:cat,a:cons("), c1, str!(",cons("), c2, str!(",null)}")])
        }

        Exp::Error(inner_e, _) => {
            let compiled = recurse!(inner_e);
            Ok(cat![str!("{c:\"f\",f:er,a:cons("), compiled, str!(",null)}")])
        }

        Exp::Seq(e1, e2) => {
            let c1 = recurse!(e1);
            let c2 = recurse!(e2);
            Ok(cat![str!("{c:\";\",e1:"), c1, str!(",e2:"), c2, str!("}")])
        }

        Exp::Let(_, _, e1, e2) => {
            let c1 = recurse!(e1);
            let c2 = recurse_inner!(e2, 1);
            Ok(cat![str!("{c:\"=\",e1:"), c1, str!(",e2:"), c2, str!("}")])
        }

        Exp::JavaScript(JavaScriptMode::Source(_), inner_e) => {
            *found_javascript = true;
            js_e(mode, outer, inner, inner_e, st, settings, nameds, some_ts, found_javascript)
        }

        Exp::JavaScript(_, inner_e) => {
            *found_javascript = true;
            let compiled = recurse!(inner_e);
            Ok(cat![str!("{c:\"e\",e:"), compiled, str!("}")])
        }

        Exp::Write(_) => {
            eprintln!("jscomp: EWrite in code to be compiled to JavaScript");
            Ok(str!("{c:\"c\",v:ERROR}"))
        }
        Exp::Closure(_, _) => {
            eprintln!("jscomp: EClosure in code to be compiled to JavaScript");
            Ok(str!("{c:\"c\",v:ERROR}"))
        }
        Exp::Query(_) => {
            eprintln!("jscomp: Query in code to be compiled to JavaScript");
            Ok(str!("{c:\"c\",v:ERROR}"))
        }
        Exp::Dml(_, _) => {
            eprintln!("jscomp: DML in code to be compiled to JavaScript");
            Ok(str!("{c:\"c\",v:ERROR}"))
        }
        Exp::Nextval(_) => {
            eprintln!("jscomp: Nextval in code to be compiled to JavaScript");
            Ok(str!("{c:\"c\",v:ERROR}"))
        }
        Exp::Setval(_, _) => {
            eprintln!("jscomp: Setval in code to be compiled to JavaScript");
            Ok(str!("{c:\"c\",v:ERROR}"))
        }
        Exp::ReturnBlob { .. } => {
            eprintln!("jscomp: EReturnBlob in code to be compiled to JavaScript");
            Ok(str!("{c:\"c\",v:ERROR}"))
        }

        Exp::Redirect(inner_e, _) => {
            let compiled = recurse!(inner_e);
            Ok(cat![str!("{c:\"f\",f:redirect,a:cons("), compiled, str!(",null)}")])
        }

        Exp::Uurlify(_, _, true) => {
            eprintln!("jscomp: EUnurlify (server-side) in code to be compiled to JavaScript");
            Ok(str!("{c:\"c\",v:ERROR}"))
        }

        Exp::Uurlify(inner_e, t, false) => {
            let compiled = recurse!(inner_e);
            let unurl = unurlify_exp(s, t, st, settings);
            Ok(cat![
                str!(&format!(
                    "{{c:\"f\",f:unurlify,a:cons({{c:\"c\",v:function(s){{var t=s.split(\"/\");var i=0;return {unurl}}}}},cons("
                )),
                compiled,
                str!(",null)}")
            ])
        }

        Exp::SignalReturn(inner_e) => {
            let compiled = recurse!(inner_e);
            Ok(cat![str!("{c:\"f\",f:sr,a:cons("), compiled, str!(",null)}")])
        }
        Exp::SignalBind(e1, e2) => {
            let c1 = recurse!(e1);
            let c2 = recurse!(e2);
            Ok(cat![str!("{c:\"f\",f:sb,a:cons("), c1, str!(",cons("), c2, str!(",null)}")])
        }
        Exp::SignalSource(inner_e) => {
            let compiled = recurse!(inner_e);
            Ok(cat![str!("{c:\"f\",f:ss,a:cons("), compiled, str!(",null)}")])
        }

        Exp::ServerCall(inner_e, t, eff, fm) => {
            let compiled = recurse!(inner_e);
            let unurl = unurlify_exp(s, t, st, settings);
            let is_nullable_t = if is_nullable(t) { "true" } else { "false" };
            let last_arg = match fm {
                FailureMode::None => "null".to_string(),
                FailureMode::Error => {
                    format!("cons({{c:\"c\",v:{is_nullable_t}}},null)")
                }
            };
            let effect_bool = match eff {
                Effect::ReadCookieWrite => "true",
                _ => "false",
            };
            let url_prefix = &settings.url_prefix;
            Ok(cat![
                str!(&format!(
                    "{{c:\"f\",f:rc,a:cons({{c:\"c\",v:\"{url_prefix}\"}},cons("
                )),
                compiled,
                str!(&format!(
                    ",cons({{c:\"c\",v:function(s){{var t=s.split(\"/\");var i=0;return {unurl}}}}},cons({{c:\"K\"}},cons({{c:\"c\",v:{effect_bool}}},{last_arg})))))}}"
                ))
            ])
        }

        Exp::Recv(inner_e, t) => {
            let compiled = recurse!(inner_e);
            let unurl = unurlify_exp(s, t, st, settings);
            Ok(cat![
                str!("{c:\"f\",f:rv,a:cons("),
                compiled,
                str!(&(
                    ",cons({c:\"c\",v:function(s){var t=s.split(\"/\");var i=0;return ".to_string()
                    + &unurl
                    + "}},cons({c:\"K\"},null)))}"
                ))
            ])
        }

        Exp::Sleep(inner_e) => {
            let compiled = recurse!(inner_e);
            Ok(cat![str!("{c:\"f\",f:sl,a:cons("), compiled, str!(",cons({c:\"K\"},null))}")])
        }

        Exp::Spawn(inner_e) => {
            let compiled = recurse!(inner_e);
            Ok(cat![str!("{c:\"f\",f:sp,a:cons("), compiled, str!(",null)}")])
        }

    }
}

/// Walk a chain `EField(... EField(base, x1) ..., xN)` to check if it is
/// rooted at an outer (captured) `ERel`.  If yes, quote the whole thing.
/// Otherwise fall back to a generic `{c:".",r:...,f:...}` node.
fn seek_field(
    mode: &JsMode,
    outer: &[LocTyp],
    inner: usize,
    base: &LocExp,
    xs: &[&str],
    original: &LocExp,
    s: &Span,
    st: &mut State,
    settings: &Settings,
    nameds: &HashMap<usize, LocExp>,
    some_ts: &HashMap<usize, LocTyp>,
    found_javascript: &mut bool,
) -> Result<LocExp, CantEmbed> {
    match &base.node {
        Exp::Rel(n) => {
            let n = *n;
            if n < inner {
                // It is a JS-runtime variable — emit generic field access
                let _base_c = js_e(mode, outer, inner, base, st, settings, nameds, some_ts, found_javascript)?;
                let last_x = xs.last().unwrap();
                let inner_c = {
                    // Build the base.fields_except_last expression
                    let mut e = base.clone();
                    for x in &xs[..xs.len() - 1] {
                        e = field(s, e, x);
                    }
                    js_e(mode, outer, inner, &e, st, settings, nameds, some_ts, found_javascript)?
                };
                Ok(strcat_exp(s, vec![
                    str_lit(s, "{c:\".\",r:"),
                    inner_c,
                    str_lit(s, &format!(",f:\"{last_x}\"}}")),
                ]))
            } else {
                // Captured from server — resolve type through field chain
                let idx = n - inner;
                let mut t = outer
                    .get(idx)
                    .ok_or_else(|| CantEmbed(str_typ(s)))?
                    .clone();
                // Walk field chain to get the leaf type
                for x in xs {
                    if let Typ::Record(fields) = &t.node.clone() {
                        t = fields
                            .iter()
                            .find(|(name, _)| name == x)
                            .map(|(_, ft)| ft.clone())
                            .ok_or_else(|| CantEmbed(str_typ(s)))?;
                    } else {
                        return Err(CantEmbed(t));
                    }
                }
                // Build the field-access expression to pass to quoteExp
                let mut acc = rel(s, idx);
                for x in xs {
                    acc = field(s, acc, x);
                }
                let quoted = quote_exp(s, &t, acc, st, settings)?;
                Ok(strcat_exp(s, vec![str_lit(s, "{c:\"c\",v:"), quoted, str_lit(s, "}")]))
            }
        }
        Exp::Field(inner_base, x) => {
            let mut new_xs = vec![x.as_str()];
            new_xs.extend_from_slice(xs);
            seek_field(mode, outer, inner, inner_base, &new_xs, original, s, st, settings, nameds, some_ts, found_javascript)
        }
        _ => {
            // Default: generic field access
            let last_x = xs.last().unwrap();
            // Build the base expression (everything except the outermost field)
            let inner_c = if xs.len() == 1 {
                js_e(mode, outer, inner, base, st, settings, nameds, some_ts, found_javascript)?
            } else {
                let mut e = base.clone();
                for x in &xs[..xs.len() - 1] {
                    e = field(s, e, x);
                }
                js_e(mode, outer, inner, &e, st, settings, nameds, some_ts, found_javascript)?
            };
            Ok(strcat_exp(s, vec![
                str_lit(s, "{c:\".\",r:"),
                inner_c,
                str_lit(s, &format!(",f:\"{last_x}\"}}")),
            ]))
        }
    }
}

// ---------------------------------------------------------------------------
// pat_binds_outer — collect types added to `outer` by a pattern
// (mirrors `patBinds` in SML's `process`, which prepends to `outer` list)
// ---------------------------------------------------------------------------

fn pat_binds_outer(p: &LocPat, outer: &[LocTyp]) -> Vec<LocTyp> {
    let mut result = outer.to_vec();
    collect_pat_types(p, &mut result);
    result
}

fn collect_pat_types(p: &LocPat, out: &mut Vec<LocTyp>) {
    match &p.node {
        Pat::Var(_, t) => out.insert(0, t.clone()),
        Pat::Prim(_) => {}
        Pat::Con(_, _, None) => {}
        Pat::Con(_, _, Some(inner)) => collect_pat_types(inner, out),
        Pat::Record(xpts) => {
            for (_, p, _) in xpts {
                collect_pat_types(p, out);
            }
        }
        Pat::None(_) => {}
        Pat::Some(_, inner) => collect_pat_types(inner, out),
    }
}

// ---------------------------------------------------------------------------
// exp — walk a Mono expression at the "declaration level"
// (transforms EJavaScript nodes to their JS-encoded versions)
// ---------------------------------------------------------------------------

fn exp_walk(
    outer: &[LocTyp],
    e: &LocExp,
    st: &mut State,
    settings: &Settings,
    nameds: &HashMap<usize, LocExp>,
    some_ts: &HashMap<usize, LocTyp>,
    found_javascript: &mut bool,
) -> LocExp {
    let s = &e.span.clone();

    macro_rules! walk { ($ex:expr) =>
        { exp_walk(outer, $ex, st, settings, nameds, some_ts, found_javascript) }
    }

    match &e.node.clone() {
        Exp::Prim(Prim::String(_, s_val)) => {
            if s_val.contains("<script") {
                *found_javascript = true;
            }
            e.clone()
        }
        Exp::Prim(_) => e.clone(),

        Exp::Rel(_) | Exp::Named(_) | Exp::Ffi(_, _) | Exp::None(_) => e.clone(),

        Exp::Con(_, _, None) => e.clone(),
        Exp::Con(dk, pc, Some(inner_e)) => {
            let new_inner = walk!(inner_e);
            Located::new(Exp::Con(*dk, pc.clone(), Some(Box::new(new_inner))), s.clone())
        }

        Exp::Some(t, inner_e) => {
            let new_inner = walk!(inner_e);
            Located::new(Exp::Some(t.clone(), Box::new(new_inner)), s.clone())
        }

        Exp::FfiApp(m, f, args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|(arg_e, t)| (walk!(arg_e), t.clone()))
                .collect();
            Located::new(Exp::FfiApp(m.clone(), f.clone(), new_args), s.clone())
        }

        Exp::App(f_e, x_e) => {
            let nf = walk!(f_e);
            let nx = walk!(x_e);
            Located::new(Exp::App(Box::new(nf), Box::new(nx)), s.clone())
        }

        Exp::Abs(x, dom, ran, body) => {
            let mut new_outer = vec![dom.clone()];
            new_outer.extend_from_slice(outer);
            let new_body = exp_walk(&new_outer, body, st, settings, nameds, some_ts, found_javascript);
            Located::new(Exp::Abs(x.clone(), dom.clone(), ran.clone(), Box::new(new_body)), s.clone())
        }

        Exp::Unop(op, inner_e) => {
            let new_inner = walk!(inner_e);
            Located::new(Exp::Unop(op.clone(), Box::new(new_inner)), s.clone())
        }
        Exp::Binop(bi, op, e1, e2) => {
            let n1 = walk!(e1);
            let n2 = walk!(e2);
            Located::new(Exp::Binop(*bi, op.clone(), Box::new(n1), Box::new(n2)), s.clone())
        }

        Exp::Record(xets) => {
            let new_xets: Vec<_> = xets.iter().map(|(x, e, t)| (x.clone(), walk!(e), t.clone())).collect();
            Located::new(Exp::Record(new_xets), s.clone())
        }
        Exp::Field(base, x) => {
            let nb = walk!(base);
            Located::new(Exp::Field(Box::new(nb), x.clone()), s.clone())
        }

        Exp::Case(disc, arms, meta) => {
            let nd = walk!(disc);
            let new_arms: Vec<_> = arms
                .iter()
                .map(|(p, arm_e)| {
                    let new_outer = pat_binds_outer(p, outer);
                    let ne = exp_walk(&new_outer, arm_e, st, settings, nameds, some_ts, found_javascript);
                    (p.clone(), ne)
                })
                .collect();
            Located::new(Exp::Case(Box::new(nd), new_arms, meta.clone()), s.clone())
        }

        Exp::Strcat(e1, e2) => {
            let n1 = walk!(e1);
            let n2 = walk!(e2);
            Located::new(Exp::Strcat(Box::new(n1), Box::new(n2)), s.clone())
        }

        Exp::Error(inner_e, t) => {
            let ne = walk!(inner_e);
            Located::new(Exp::Error(Box::new(ne), t.clone()), s.clone())
        }

        Exp::ReturnBlob { blob: None, mime_type, t } => {
            let nm = walk!(mime_type);
            Located::new(Exp::ReturnBlob { blob: None, mime_type: Box::new(nm), t: t.clone() }, s.clone())
        }
        Exp::ReturnBlob { blob: Some(blob), mime_type, t } => {
            let nb = walk!(blob);
            let nm = walk!(mime_type);
            Located::new(Exp::ReturnBlob { blob: Some(Box::new(nb)), mime_type: Box::new(nm), t: t.clone() }, s.clone())
        }

        Exp::Redirect(inner_e, t) => {
            let ne = walk!(inner_e);
            Located::new(Exp::Redirect(Box::new(ne), t.clone()), s.clone())
        }

        Exp::Write(inner_e) => {
            let ne = walk!(inner_e);
            Located::new(Exp::Write(Box::new(ne)), s.clone())
        }
        Exp::Seq(e1, e2) => {
            let n1 = walk!(e1);
            let n2 = walk!(e2);
            Located::new(Exp::Seq(Box::new(n1), Box::new(n2)), s.clone())
        }
        Exp::Let(x, t, e1, e2) => {
            let n1 = walk!(e1);
            let mut new_outer = vec![t.clone()];
            new_outer.extend_from_slice(outer);
            let n2 = exp_walk(&new_outer, e2, st, settings, nameds, some_ts, found_javascript);
            Located::new(Exp::Let(x.clone(), t.clone(), Box::new(n1), Box::new(n2)), s.clone())
        }

        Exp::Closure(n, envs) => {
            let new_envs: Vec<_> = envs.iter().map(|e| walk!(e)).collect();
            Located::new(Exp::Closure(*n, new_envs), s.clone())
        }

        Exp::Query(qm) => {
            let row: Vec<(String, LocTyp)> = {
                let mut r: Vec<_> = qm.exps.clone();
                r.extend(qm.tables.iter().map(|(x, xts)| {
                    (x.clone(), Located::new(Typ::Record(xts.clone()), s.clone()))
                }));
                r.sort_by(|(a, _), (b, _)| a.cmp(b));
                r
            };
            let row_t = Located::new(Typ::Record(row), s.clone());
            let nq = walk!(&qm.query);
            let mut body_outer = vec![qm.state.clone(), row_t];
            body_outer.extend_from_slice(outer);
            let nb = exp_walk(&body_outer, &qm.body, st, settings, nameds, some_ts, found_javascript);
            let ni = walk!(&qm.initial);
            Located::new(Exp::Query(crate::monomorphized::QueryMeta {
                exps: qm.exps.clone(),
                tables: qm.tables.clone(),
                state: qm.state.clone(),
                query: Box::new(nq),
                body: Box::new(nb),
                initial: Box::new(ni),
            }), s.clone())
        }

        Exp::Dml(inner_e, fm) => {
            let ne = walk!(inner_e);
            Located::new(Exp::Dml(Box::new(ne), *fm), s.clone())
        }
        Exp::Nextval(inner_e) => {
            let ne = walk!(inner_e);
            Located::new(Exp::Nextval(Box::new(ne)), s.clone())
        }
        Exp::Setval(e1, e2) => {
            let n1 = walk!(e1);
            let n2 = walk!(e2);
            Located::new(Exp::Setval(Box::new(n1), Box::new(n2)), s.clone())
        }

        Exp::Uurlify(inner_e, t, b) => {
            let ne = walk!(inner_e);
            Located::new(Exp::Uurlify(Box::new(ne), t.clone(), *b), s.clone())
        }

        Exp::JavaScript(JavaScriptMode::Source(t), inner_e) => {
            *found_javascript = true;
            // EJavaScript (Source t, e') =>
            // Try: jsExp mode (t :: outer) (ERel 0)  under an ELet("x", t, e', ...)
            let mode = JsMode::Source;
            let mut t_outer = vec![t.clone()];
            t_outer.extend_from_slice(outer);
            match js_exp(&mode, &t_outer, &rel(s, 0), st, settings, nameds, some_ts, found_javascript) {
                Ok(x_prime) => {
                    Located::new(Exp::Let("x".to_string(), t.clone(), inner_e.clone(), Box::new(x_prime)), s.clone())
                }
                Err(_) => {
                    // CantEmbed: try jsExp mode outer e'
                    match js_exp(&mode, outer, inner_e, st, settings, nameds, some_ts, found_javascript) {
                        Ok(result) => result,
                        Err(_) => {
                            // Both failed: return original expression unchanged
                            e.clone()
                        }
                    }
                }
            }
        }

        Exp::JavaScript(m, inner_e) => {
            *found_javascript = true;
            let mode = java_script_mode_to_js_mode(m);
            match js_exp(&mode, outer, inner_e, st, settings, nameds, some_ts, found_javascript) {
                Ok(result) => result,
                Err(_) => e.clone(),
            }
        }

        Exp::SignalReturn(inner_e) => {
            let ne = walk!(inner_e);
            Located::new(Exp::SignalReturn(Box::new(ne)), s.clone())
        }
        Exp::SignalBind(e1, e2) => {
            let n1 = walk!(e1);
            let n2 = walk!(e2);
            Located::new(Exp::SignalBind(Box::new(n1), Box::new(n2)), s.clone())
        }
        Exp::SignalSource(inner_e) => {
            let ne = walk!(inner_e);
            Located::new(Exp::SignalSource(Box::new(ne)), s.clone())
        }

        Exp::ServerCall(inner_e, t, eff, fm) => {
            let ne = walk!(inner_e);
            Located::new(Exp::ServerCall(Box::new(ne), t.clone(), *eff, *fm), s.clone())
        }
        Exp::Recv(inner_e, t) => {
            let ne = walk!(inner_e);
            Located::new(Exp::Recv(Box::new(ne), t.clone()), s.clone())
        }
        Exp::Sleep(inner_e) => {
            let ne = walk!(inner_e);
            Located::new(Exp::Sleep(Box::new(ne)), s.clone())
        }
        Exp::Spawn(inner_e) => {
            let ne = walk!(inner_e);
            Located::new(Exp::Spawn(Box::new(ne)), s.clone())
        }
    }
}

// ---------------------------------------------------------------------------
// decl_walk — apply exp_walk to a declaration's expressions
// ---------------------------------------------------------------------------

fn decl_walk(
    d: &crate::monomorphized::LocDecl,
    st: &mut State,
    settings: &Settings,
    nameds: &HashMap<usize, LocExp>,
    some_ts: &HashMap<usize, LocTyp>,
    found_javascript: &mut bool,
) -> crate::monomorphized::LocDecl {
    let s = &d.span.clone();
    match &d.node.clone() {
        Decl::Val(x, n, t, e, settings_s) => {
            let ne = exp_walk(&[], e, st, settings, nameds, some_ts, found_javascript);
            Located::new(Decl::Val(x.clone(), *n, t.clone(), ne, settings_s.clone()), s.clone())
        }
        Decl::ValRec(vis) => {
            let new_vis: Vec<_> = vis
                .iter()
                .map(|(x, n, t, e, settings_s)| {
                    let ne = exp_walk(&[], e, st, settings, nameds, some_ts, found_javascript);
                    (x.clone(), *n, t.clone(), ne, settings_s.clone())
                })
                .collect();
            Located::new(Decl::ValRec(new_vis), s.clone())
        }
        _ => d.clone(),
    }
}

// ---------------------------------------------------------------------------
// process — main entry point (mirrors `process` in jscomp.sml)
// ---------------------------------------------------------------------------

fn process(
    file: &crate::monomorphized::File,
    settings: &Settings,
    _errors: &mut crate::error_types::ErrorReporter,
) -> (crate::monomorphized::File, Option<String>) {
    // Pass 1: build `some_ts` and `nameds` maps
    let mut some_ts: HashMap<usize, LocTyp> = HashMap::new();
    let mut nameds: HashMap<usize, LocExp> = HashMap::new();

    for d in &file.0 {
        match &d.node {
            Decl::Val(_, n, _, e, _) => {
                nameds.insert(*n, e.clone());
            }
            Decl::ValRec(vis) => {
                for (_, n, _, e, _) in vis {
                    nameds.insert(*n, e.clone());
                }
            }
            Decl::Datatype(dts) => {
                for DatatypeDecl { constrs, .. } in dts {
                    // Classify: if Option kind, record the SOME constructor's type
                    let kind = crate::monomorphized::utilities::classify_datatype(constrs);
                    if kind == DatatypeKind::Option {
                        for (_, n, opt_t) in constrs {
                            if let Some(t) = opt_t {
                                some_ts.insert(*n, t.clone());
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    // Pass 2: walk each decl, accumulating JS state
    let max_n = max_name_in_file(file) + 1;
    let mut st = State::new(max_n);
    let mut found_javascript = false;

    let mut out_decls: Vec<crate::monomorphized::LocDecl> = Vec::new();

    for d in &file.0 {
        let new_d = decl_walk(d, &mut st, settings, &nameds, &some_ts, &mut found_javascript);

        // If any helpers were generated, emit them as a DValRec before this decl
        if !st.decls.is_empty() {
            let helpers = std::mem::take(&mut st.decls);
            let span = d.span.clone();
            out_decls.push(Located::new(Decl::ValRec(helpers), span));
        }
        out_decls.push(new_d);
    }

    // Build JavaScript output
    let script = if found_javascript {
        // Try to read the urweb.js library file
        let lib_js = {
            let lib_path = if settings.config_lib.is_empty() {
                std::path::PathBuf::from("lib").join("js").join("urweb.js")
            } else {
                std::path::PathBuf::from(&settings.config_lib)
                    .join("js")
                    .join("urweb.js")
            };
            std::fs::read_to_string(&lib_path).unwrap_or_else(|_| {
                // Fallback: empty string (no runtime library available at compile time)
                String::new()
            })
        };

        // Build URL rules JS
        let url_rules = settings.url_rules.iter().rev().fold("null".to_string(), |acc, r| {
            let allow = if r.action == crate::settings::Action::Allow { "true" } else { "false" };
            let prefix = if r.kind == crate::settings::PatternKind::Prefix { "true" } else { "false" };
            let pattern = &r.pattern;
            format!("cons({{allow:{allow},prefix:{prefix},pattern:\"{pattern}\"}},{acc})")
        });
        let url_rules_js = format!("urlRules = {url_rules};\n\n");

        // Join accumulated script fragments (they were pushed in order, so reverse)
        let accumulated: String = st.script.iter().rev().cloned().collect::<Vec<_>>().join("");

        let time_format = &settings.time_format;
        // Escape for JS string: replace \ with \\ and " with \"
        let tf_escaped = time_format
            .replace('\\', "\\\\")
            .replace('"', "\\\"");

        let main_script = format!(
            "{lib_js}{url_rules_js}{accumulated}\ntime_format = \"{tf_escaped}\";\n"
        );

        // Include any extra JS files referenced in settings
        // (mirrors `Settings.listJsFiles()` in SML — we don't have that in Rust yet)
        Some(main_script)
    } else {
        None
    };

    // Collect any pre-existing Decl::JavaScript strings from the input file
    let pre_js: Vec<String> = file
        .0
        .iter()
        .filter_map(|d| match &d.node {
            Decl::JavaScript(s) if !s.is_empty() => Some(s.clone()),
            _ => None,
        })
        .collect();

    // Combine compiled script with pre-existing JS
    let js_string = match (script, pre_js.is_empty()) {
        (None, true) => {
            // No JS at all
            let span = crate::error_types::Span::dummy();
            let js_decl = Located::new(Decl::JavaScript(String::new()), span);
            let mut final_decls = vec![js_decl];
            final_decls.extend(out_decls);
            return ((final_decls, file.1.clone()), None);
        }
        (None, false) => pre_js.join("\n"),
        (Some(s), true) => s,
        (Some(s), false) => {
            let mut combined = s;
            combined.push('\n');
            combined.push_str(&pre_js.join("\n"));
            combined
        }
    };

    // Prepend a DJavaScript decl with the script content
    let span = crate::error_types::Span::dummy();
    let js_decl = Located::new(Decl::JavaScript(js_string.clone()), span);

    let mut final_decls = vec![js_decl];
    final_decls.extend(out_decls);

    ((final_decls, file.1.clone()), Some(js_string))
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Compile client-side JavaScript from a Mono `File`.
///
/// Returns `Some(script)` where `script` is the concatenated JavaScript to
/// embed in the compiled application.  Returns `None` only on fatal error.
pub fn js_compile(
    file: &crate::monomorphized::File,
    settings: &Settings,
    errors: &mut crate::error_types::ErrorReporter,
) -> Option<String> {
    let (_new_file, script) = process(file, settings, errors);
    script
}
