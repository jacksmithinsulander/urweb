//! Small helpers and enums used only from `grammar.lalrpop` (LALRPOP allows only `use` before `grammar;`).

use crate::error_types::{Located, Span};
use crate::primitives::Prim;
use crate::source::{Con, Exp, Inference, Kind, LocCon, LocExp, LocPat, Pat};

#[derive(Clone)]
pub enum SqlSelectItem {
    Expression {
        alias_name: String,
        expression: LocExp,
    },
    Fields {
        table_name: String,
        fields: LocCon,
    },
}

#[derive(Clone)]
pub enum SqlSelectSpec {
    Star,
    Items(Vec<SqlSelectItem>),
}

#[derive(Clone, Copy)]
pub enum SqlJoinKind {
    Inner,
    Left,
}

/// Build [`Exp::Var`] from a dotted path string (`Foo.bar.baz` → quals + final name) after `@` / `@@`.
pub fn exp_var_from_dotted_at_path(dotted: String, inference: Inference) -> Exp {
    let mut segments: Vec<String> = dotted.split('.').map(String::from).collect();
    let final_name = segments
        .pop()
        .expect("dotted @-path from lexer always has at least one segment");
    Exp::Var(segments, final_name, inference)
}

/// `Pat = PatCore PatOptAnn?` in one production so `:` after `PatCore` is never a reduce/shift
/// split between two `Pat` rules (LangSec / LR(1)).
pub fn fold_pat_opt_ann(l: usize, r: usize, p: Pat, ann: Option<LocCon>) -> LocPat {
    let span = Span::from_offsets("", l, r, &[]);
    match ann {
        None => Located::new(p, span),
        Some(c) => Located::new(Pat::Annot(Box::new(Located::dummy(p)), c), span),
    }
}

/// Left-fold relational operators: `AddExp (relop AddExp)*` without left-recursive `CmpExp`.
pub fn fold_cmp_rel_chain(first: LocExp, tail: Vec<(String, LocExp)>) -> LocExp {
    let mut acc = first;
    for (op, rhs) in tail {
        let l = acc.span.first.clone();
        let r = rhs.span.last.clone();
        let file = acc.span.file.clone();
        acc = Located::new(
            Exp::Infix(op, Box::new(acc), Box::new(rhs)),
            Span {
                file,
                first: l,
                last: r,
            },
        );
    }
    acc
}

/// Left-fold `andalso` / `orelse` after `BoolExp` (no left-recursive `NonSeqExp`).
pub fn fold_nonseq_chain(mut acc: LocExp, tail: Vec<(bool, LocExp)>) -> Exp {
    for (is_andalso, rhs) in tail {
        acc = if is_andalso {
            Located::new(
                Exp::Case(
                    Box::new(acc),
                    vec![
                        (
                            Located::dummy(Pat::Con(vec!["Basis".into()], "True".into(), None)),
                            rhs,
                        ),
                        (
                            Located::dummy(Pat::Con(vec!["Basis".into()], "False".into(), None)),
                            Located::dummy(Exp::Var(
                                vec!["Basis".into()],
                                "False".into(),
                                Inference::DontInfer,
                            )),
                        ),
                    ],
                ),
                Span::dummy(),
            )
        } else {
            Located::new(
                Exp::Case(
                    Box::new(acc),
                    vec![
                        (
                            Located::dummy(Pat::Con(vec!["Basis".into()], "True".into(), None)),
                            Located::dummy(Exp::Var(
                                vec!["Basis".into()],
                                "True".into(),
                                Inference::DontInfer,
                            )),
                        ),
                        (
                            Located::dummy(Pat::Con(vec!["Basis".into()], "False".into(), None)),
                            rhs,
                        ),
                    ],
                ),
                Span::dummy(),
            )
        };
    }
    acc.node
}

/// `urweb.grm` `rconn`: bare `rpath` fields default to unit (or pun for lowercase symbols).
pub fn con_record_field_pun(name: LocCon) -> (LocCon, LocCon) {
    match &name.node {
        Con::Var(ms, x)
            if ms.is_empty() && x.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) =>
        {
            let name_con = Located::dummy(Con::Name(x.clone()));
            (name_con, Located::dummy(Con::Unit))
        }
        _ => (name.clone(), name),
    }
}

/// Desugar monadic bind syntax `x <- e1; e2` to `Basis.bind e1 (fn x => e2)`.
pub fn desugar_monadic_bind(bound_name: String, bound_expression: LocExp, body: LocExp) -> Exp {
    let bind_var = Located::new(
        Exp::Var(vec!["Basis".into()], "bind".into(), Inference::Infer),
        bound_expression.span.clone(),
    );
    let bind_apply = Located::new(
        Exp::App(Box::new(bind_var), Box::new(bound_expression)),
        Span::dummy(),
    );
    let lambda = Located::new(Exp::Abs(bound_name, None, Box::new(body)), Span::dummy());
    Exp::App(Box::new(bind_apply), Box::new(lambda))
}

fn basis_var_expression(name: &str, span: &Span) -> LocExp {
    Located::new(
        Exp::Var(vec!["Basis".into()], name.to_string(), Inference::Infer),
        span.clone(),
    )
}

fn basis_name_constructor(name: &str, span: &Span) -> LocCon {
    Located::new(Con::Name(name.to_string()), span.clone())
}

fn apply_expression(function: LocExp, argument: LocExp, span: &Span) -> LocExp {
    Located::new(
        Exp::App(Box::new(function), Box::new(argument)),
        span.clone(),
    )
}

fn constructor_apply_expression(function: LocExp, argument: LocCon, span: &Span) -> LocExp {
    Located::new(Exp::CApp(Box::new(function), argument), span.clone())
}

fn empty_row_constructor(span: &Span) -> LocCon {
    Located::new(Con::Record(Vec::new()), span.clone())
}

fn unit_constructor(span: &Span) -> LocCon {
    Located::new(Con::Unit, span.clone())
}

fn wildcard_type_record_kind(span: &Span) -> Kind {
    Kind::Record(Box::new(Located::new(Kind::Type, span.clone())))
}

fn wildcard_table_record_kind(span: &Span) -> Kind {
    Kind::Record(Box::new(Located::new(
        Kind::Record(Box::new(Located::new(Kind::Type, span.clone()))),
        span.clone(),
    )))
}

fn tuple_constructor(parts: Vec<LocCon>, span: &Span) -> LocCon {
    Located::new(Con::Tuple(parts), span.clone())
}

fn row_record_constructor(fields: Vec<(LocCon, LocCon)>, span: &Span) -> LocCon {
    Located::new(Con::Record(fields), span.clone())
}

fn record_expression(fields: Vec<(LocCon, LocExp)>, span: &Span) -> LocExp {
    Located::new(Exp::Record(fields, false), span.clone())
}

fn basis_bool_expression(value: bool, span: &Span) -> LocExp {
    match value {
        true => basis_var_expression("True", span),
        false => basis_var_expression("False", span),
    }
}

fn capitalize_identifier(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
}

fn sql_name_from_surface(name: &str) -> String {
    capitalize_identifier(name)
}

fn sql_name_constructor(name: &str, span: &Span) -> LocCon {
    basis_name_constructor(&sql_name_from_surface(name), span)
}

pub fn sql_inject_expression(value: LocExp, span: &Span) -> LocExp {
    let inject = basis_var_expression("sql_inject", span);
    apply_expression(inject, value, span)
}

pub fn sql_binary_expression(
    operator_name: &str,
    left: LocExp,
    right: LocExp,
    span: &Span,
) -> LocExp {
    let binary = basis_var_expression("sql_binary", span);
    let operator = basis_var_expression(&format!("sql_{operator_name}"), span);
    let apply_operator = apply_expression(binary, operator, span);
    let apply_left = apply_expression(apply_operator, left, span);
    apply_expression(apply_left, right, span)
}

pub fn sql_is_null_expression(value: LocExp, span: &Span) -> LocExp {
    let is_null = basis_var_expression("sql_is_null", span);
    apply_expression(is_null, value, span)
}

pub fn sql_count_all_expression(span: &Span) -> LocExp {
    basis_var_expression("sql_count", span)
}

pub fn sql_current_timestamp_expression(span: &Span) -> LocExp {
    let sql_nfunc = basis_var_expression("sql_nfunc", span);
    let current_timestamp = basis_var_expression("sql_current_timestamp", span);
    apply_expression(sql_nfunc, current_timestamp, span)
}

pub fn sql_integer_expression(value: i64, span: &Span) -> LocExp {
    sql_inject_expression(
        Located::new(Exp::Prim(Prim::Int(value)), span.clone()),
        span,
    )
}

pub fn sql_wrap_window_expression(value: LocExp, span: &Span) -> LocExp {
    let window = basis_var_expression("sql_window", span);
    apply_expression(window, value, span)
}

pub fn sql_table_reference(name: String, span: &Span) -> (String, LocExp) {
    (
        capitalize_identifier(&name),
        Located::new(Exp::Var(vec![], name, Inference::Infer), span.clone()),
    )
}

pub fn sql_table_reference_with_alias(
    table_name: String,
    alias_name: Option<String>,
    span: &Span,
) -> (Vec<String>, LocExp) {
    let alias_surface = match alias_name {
        Some(alias) => alias,
        None => table_name.clone(),
    };
    let alias_name = sql_name_from_surface(&alias_surface);
    let table_expression =
        Located::new(Exp::Var(vec![], table_name, Inference::Infer), span.clone());
    let from_table = constructor_apply_expression(
        basis_var_expression("sql_from_table", span),
        sql_name_constructor(&alias_name, span),
        span,
    );
    (
        vec![alias_name],
        apply_expression(from_table, table_expression, span),
    )
}

pub fn sql_field_expression(table_name: String, field_name: String, span: &Span) -> LocExp {
    let by_table = constructor_apply_expression(
        basis_var_expression("sql_field", span),
        sql_name_constructor(&table_name, span),
        span,
    );
    constructor_apply_expression(by_table, sql_name_constructor(&field_name, span), span)
}

pub fn sql_dynamic_field_expression(table_name: String, field_name: LocCon, span: &Span) -> LocExp {
    let by_table = constructor_apply_expression(
        basis_var_expression("sql_field", span),
        sql_name_constructor(&table_name, span),
        span,
    );
    constructor_apply_expression(by_table, field_name, span)
}

pub fn sql_default_table_field_expression(field_name: String, span: &Span) -> LocExp {
    sql_field_expression("T".to_string(), field_name, span)
}

fn sql_order_by_nil_expression(span: &Span) -> LocExp {
    constructor_apply_expression(
        basis_var_expression("sql_order_by_Nil", span),
        Located::new(
            Con::Wild(Box::new(Located::new(
                wildcard_type_record_kind(span),
                span.clone(),
            ))),
            span.clone(),
        ),
        span,
    )
}

fn sql_subset_all_expression(span: &Span) -> LocExp {
    constructor_apply_expression(
        basis_var_expression("sql_subset_all", span),
        Located::new(
            Con::Wild(Box::new(Located::new(
                wildcard_table_record_kind(span),
                span.clone(),
            ))),
            span.clone(),
        ),
        span,
    )
}

fn sql_subset_expression(subset: LocCon, span: &Span) -> LocExp {
    constructor_apply_expression(basis_var_expression("sql_subset", span), subset, span)
}

fn sql_true_expression(span: &Span) -> LocExp {
    sql_inject_expression(basis_bool_expression(true, span), span)
}

fn sql_wild_type_row(span: &Span) -> LocCon {
    Located::new(
        Con::Wild(Box::new(Located::new(
            wildcard_type_record_kind(span),
            span.clone(),
        ))),
        span.clone(),
    )
}

fn sql_is_empty_row(row: &LocCon) -> bool {
    matches!(row.node, Con::Record(ref fields) if fields.is_empty())
}

fn sql_concat_rows(left_row: LocCon, right_row: LocCon, span: &Span) -> LocCon {
    if sql_is_empty_row(&left_row) {
        return right_row;
    }
    if sql_is_empty_row(&right_row) {
        return left_row;
    }
    Located::new(
        Con::Concat(Box::new(left_row), Box::new(right_row)),
        span.clone(),
    )
}

fn sql_query_expression(query1: LocExp, span: &Span) -> Exp {
    let query_record = record_expression(
        vec![
            (basis_name_constructor("Rows", span), query1),
            (
                basis_name_constructor("OrderBy", span),
                sql_order_by_nil_expression(span),
            ),
            (
                basis_name_constructor("Limit", span),
                basis_var_expression("sql_no_limit", span),
            ),
            (
                basis_name_constructor("Offset", span),
                basis_var_expression("sql_no_offset", span),
            ),
        ],
        span,
    );
    Exp::App(
        Box::new(basis_var_expression("sql_query", span)),
        Box::new(query_record),
    )
}

pub fn desugar_sql_select_query(
    select_spec: SqlSelectSpec,
    from_names: Vec<String>,
    from_expression: LocExp,
    where_expression: LocExp,
    span: &Span,
) -> Exp {
    match select_spec {
        SqlSelectSpec::Star => {
            let mut selected_fields: Vec<(LocCon, LocCon)> = Vec::with_capacity(from_names.len());
            for table_name in &from_names {
                selected_fields.push((
                    basis_name_constructor(table_name, span),
                    tuple_constructor(
                        vec![sql_wild_type_row(span), empty_row_constructor(span)],
                        span,
                    ),
                ));
            }
            let query1_record = record_expression(
                vec![
                    (
                        basis_name_constructor("Distinct", span),
                        basis_bool_expression(false, span),
                    ),
                    (basis_name_constructor("From", span), from_expression),
                    (basis_name_constructor("Where", span), where_expression),
                    (
                        basis_name_constructor("GroupBy", span),
                        sql_subset_all_expression(span),
                    ),
                    (
                        basis_name_constructor("Having", span),
                        sql_true_expression(span),
                    ),
                    (
                        basis_name_constructor("SelectFields", span),
                        sql_subset_expression(row_record_constructor(selected_fields, span), span),
                    ),
                    (
                        basis_name_constructor("SelectExps", span),
                        record_expression(Vec::new(), span),
                    ),
                ],
                span,
            );
            let query1 = apply_expression(
                constructor_apply_expression(
                    basis_var_expression("sql_query1", span),
                    row_record_constructor(Vec::new(), span),
                    span,
                ),
                query1_record,
                span,
            );
            sql_query_expression(query1, span)
        }
        SqlSelectSpec::Items(select_items) => {
            let mut table_rows: Vec<(String, LocCon)> = Vec::with_capacity(from_names.len());
            let mut select_expressions: Vec<(LocCon, LocExp)> = Vec::new();
            for table_name in &from_names {
                table_rows.push((table_name.clone(), empty_row_constructor(span)));
            }
            for select_item in select_items {
                match select_item {
                    SqlSelectItem::Expression {
                        alias_name,
                        expression,
                    } => {
                        select_expressions.push((
                            basis_name_constructor(&alias_name, span),
                            sql_wrap_window_expression(expression, span),
                        ));
                    }
                    SqlSelectItem::Fields { table_name, fields } => {
                        for (existing_name, existing_fields) in &mut table_rows {
                            if *existing_name == table_name {
                                *existing_fields =
                                    sql_concat_rows(existing_fields.clone(), fields.clone(), span);
                                break;
                            }
                        }
                    }
                }
            }
            let mut empties: Vec<(LocCon, LocCon)> = Vec::new();
            let mut selected_fields: Vec<(LocCon, LocCon)> = Vec::with_capacity(table_rows.len());
            for (table_name, fields) in table_rows {
                if sql_is_empty_row(&fields) {
                    empties.push((
                        basis_name_constructor(&table_name, span),
                        unit_constructor(span),
                    ));
                }
                selected_fields.push((
                    basis_name_constructor(&table_name, span),
                    tuple_constructor(vec![fields, sql_wild_type_row(span)], span),
                ));
            }
            let query1_record = record_expression(
                vec![
                    (
                        basis_name_constructor("Distinct", span),
                        basis_bool_expression(false, span),
                    ),
                    (basis_name_constructor("From", span), from_expression),
                    (basis_name_constructor("Where", span), where_expression),
                    (
                        basis_name_constructor("GroupBy", span),
                        sql_subset_all_expression(span),
                    ),
                    (
                        basis_name_constructor("Having", span),
                        sql_true_expression(span),
                    ),
                    (
                        basis_name_constructor("SelectFields", span),
                        sql_subset_expression(row_record_constructor(selected_fields, span), span),
                    ),
                    (
                        basis_name_constructor("SelectExps", span),
                        record_expression(select_expressions, span),
                    ),
                ],
                span,
            );
            let query1 = apply_expression(
                constructor_apply_expression(
                    basis_var_expression("sql_query1", span),
                    row_record_constructor(empties, span),
                    span,
                ),
                query1_record,
                span,
            );
            sql_query_expression(query1, span)
        }
    }
}

pub fn sql_from_comma_expression(
    left: (Vec<String>, LocExp),
    right: (Vec<String>, LocExp),
    span: &Span,
) -> (Vec<String>, LocExp) {
    let mut table_names = left.0;
    table_names.extend(right.0);
    let from_comma = apply_expression(basis_var_expression("sql_from_comma", span), left.1, span);
    (table_names, apply_expression(from_comma, right.1, span))
}

pub fn sql_join_expression(
    join_kind: SqlJoinKind,
    left: (Vec<String>, LocExp),
    right: (Vec<String>, LocExp),
    predicate: LocExp,
    span: &Span,
) -> (Vec<String>, LocExp) {
    let helper_name = match join_kind {
        SqlJoinKind::Inner => "sql_inner_join",
        SqlJoinKind::Left => "sql_left_join",
    };
    let mut table_names = left.0;
    table_names.extend(right.0);
    let joined_left = apply_expression(basis_var_expression(helper_name, span), left.1, span);
    let joined_right = apply_expression(joined_left, right.1, span);
    (table_names, apply_expression(joined_right, predicate, span))
}

pub fn desugar_sql_insert_expression(
    table_name: String,
    fields: Vec<String>,
    values: Vec<LocExp>,
    span: &Span,
) -> Exp {
    let table_expression =
        Located::new(Exp::Var(vec![], table_name, Inference::Infer), span.clone());
    let insert = apply_expression(basis_var_expression("insert", span), table_expression, span);
    let mut record_fields: Vec<(LocCon, LocExp)> = Vec::with_capacity(fields.len());
    for (field_name, value_expression) in fields.into_iter().zip(values) {
        record_fields.push((sql_name_constructor(&field_name, span), value_expression));
    }
    Exp::App(
        Box::new(insert),
        Box::new(record_expression(record_fields, span)),
    )
}

pub fn desugar_sql_delete_expression(table_name: String, predicate: LocExp, span: &Span) -> Exp {
    let table_expression =
        Located::new(Exp::Var(vec![], table_name, Inference::Infer), span.clone());
    let delete = apply_expression(basis_var_expression("delete", span), table_expression, span);
    Exp::App(Box::new(delete), Box::new(predicate))
}

pub fn desugar_sql_update_expression(
    table_name: String,
    assignments: Vec<(String, LocExp)>,
    predicate: LocExp,
    span: &Span,
) -> Exp {
    let table_expression =
        Located::new(Exp::Var(vec![], table_name, Inference::Infer), span.clone());
    let wildcard_row = Located::new(
        Con::Wild(Box::new(Located::new(
            wildcard_type_record_kind(span),
            span.clone(),
        ))),
        span.clone(),
    );
    let update =
        constructor_apply_expression(basis_var_expression("update", span), wildcard_row, span);
    let mut assignment_fields: Vec<(LocCon, LocExp)> = Vec::with_capacity(assignments.len());
    for (field_name, value_expression) in assignments {
        assignment_fields.push((sql_name_constructor(&field_name, span), value_expression));
    }
    let with_assignments =
        apply_expression(update, record_expression(assignment_fields, span), span);
    let with_table = apply_expression(with_assignments, table_expression, span);
    Exp::App(Box::new(with_table), Box::new(predicate))
}

pub fn desugar_simple_sql_select(
    alias_name: String,
    selected_expression: LocExp,
    table_name: String,
    table_expression: LocExp,
    span: &Span,
) -> Exp {
    let group_subset = constructor_apply_expression(
        basis_var_expression("sql_subset_all", span),
        Located::new(
            Con::Wild(Box::new(Located::new(
                wildcard_table_record_kind(span),
                span.clone(),
            ))),
            span.clone(),
        ),
        span,
    );
    let select_fields = constructor_apply_expression(
        basis_var_expression("sql_subset", span),
        row_record_constructor(
            vec![(
                basis_name_constructor(&table_name, span),
                tuple_constructor(
                    vec![
                        empty_row_constructor(span),
                        Located::new(
                            Con::Wild(Box::new(Located::new(
                                wildcard_type_record_kind(span),
                                span.clone(),
                            ))),
                            span.clone(),
                        ),
                    ],
                    span,
                ),
            )],
            span,
        ),
        span,
    );
    let select_expressions = record_expression(
        vec![(
            basis_name_constructor(&alias_name, span),
            sql_wrap_window_expression(selected_expression, span),
        )],
        span,
    );
    let from_table = apply_expression(
        constructor_apply_expression(
            basis_var_expression("sql_from_table", span),
            basis_name_constructor(&table_name, span),
            span,
        ),
        table_expression,
        span,
    );
    let query1_record = record_expression(
        vec![
            (
                basis_name_constructor("Distinct", span),
                basis_bool_expression(false, span),
            ),
            (basis_name_constructor("From", span), from_table),
            (
                basis_name_constructor("Where", span),
                sql_inject_expression(basis_bool_expression(true, span), span),
            ),
            (basis_name_constructor("GroupBy", span), group_subset),
            (
                basis_name_constructor("Having", span),
                sql_inject_expression(basis_bool_expression(true, span), span),
            ),
            (basis_name_constructor("SelectFields", span), select_fields),
            (
                basis_name_constructor("SelectExps", span),
                select_expressions,
            ),
        ],
        span,
    );
    let query1 = apply_expression(
        constructor_apply_expression(
            basis_var_expression("sql_query1", span),
            row_record_constructor(
                vec![(
                    basis_name_constructor(&table_name, span),
                    unit_constructor(span),
                )],
                span,
            ),
            span,
        ),
        query1_record,
        span,
    );
    let query_record = record_expression(
        vec![
            (basis_name_constructor("Rows", span), query1),
            (
                basis_name_constructor("OrderBy", span),
                constructor_apply_expression(
                    basis_var_expression("sql_order_by_Nil", span),
                    Located::new(
                        Con::Wild(Box::new(Located::new(
                            wildcard_type_record_kind(span),
                            span.clone(),
                        ))),
                        span.clone(),
                    ),
                    span,
                ),
            ),
            (
                basis_name_constructor("Limit", span),
                basis_var_expression("sql_no_limit", span),
            ),
            (
                basis_name_constructor("Offset", span),
                basis_var_expression("sql_no_offset", span),
            ),
        ],
        span,
    );
    Exp::App(
        Box::new(basis_var_expression("sql_query", span)),
        Box::new(query_record),
    )
}
