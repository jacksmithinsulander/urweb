//! DB mode classification pass.
//!
//! For each export, determines whether it accesses the database at all
//! (NoDb), runs exactly one query (OneQuery), or may perform arbitrary
//! DB operations (AnyDb).
//!
//! Mirrors `DbModeCheck.classify` in `dbmodecheck.sml`.

use std::collections::HashMap;

use crate::monomorphized::{DbMode, Decl, Exp, File, LocExp, Sidedness};

// ---------------------------------------------------------------------------
// merge_modes
// ---------------------------------------------------------------------------

fn merge_modes(m1: DbMode, m2: DbMode) -> DbMode {
    match (m1, m2) {
        (DbMode::NoDb, _) => m2,
        (_, DbMode::NoDb) => m1,
        _ => DbMode::AnyDb,
    }
}

// ---------------------------------------------------------------------------
// mode_of — recursively walk an expression accumulating DB mode
// ---------------------------------------------------------------------------

fn mode_of_exp(e: &LocExp, modes: &HashMap<usize, DbMode>, acc: DbMode) -> DbMode {
    match &e.node {
        Exp::Query(_) => merge_modes(DbMode::OneQuery, acc),
        Exp::Dml(_, _) | Exp::Nextval(_) | Exp::Setval(_, _) => DbMode::AnyDb,
        Exp::Named(n) => match modes.get(n) {
            None => acc,
            Some(m) => merge_modes(acc, *m),
        },
        // Recurse into all compound expressions
        Exp::App(f, arg) => {
            let acc = mode_of_exp(f, modes, acc);
            mode_of_exp(arg, modes, acc)
        }
        Exp::Abs(_, _, _, body) => mode_of_exp(body, modes, acc),
        Exp::Let(_, _, e1, e2)
        | Exp::Seq(e1, e2)
        | Exp::Strcat(e1, e2)
        | Exp::Binop(_, _, e1, e2)
        | Exp::SignalBind(e1, e2) => {
            let acc = mode_of_exp(e1, modes, acc);
            mode_of_exp(e2, modes, acc)
        }
        Exp::Write(inner)
        | Exp::Unop(_, inner)
        | Exp::Field(inner, _)
        | Exp::SignalReturn(inner)
        | Exp::SignalSource(inner)
        | Exp::Sleep(inner)
        | Exp::Spawn(inner) => mode_of_exp(inner, modes, acc),
        Exp::FfiApp(_, _, args) => args
            .iter()
            .fold(acc, |acc, (e, _)| mode_of_exp(e, modes, acc)),
        Exp::Record(xets) => xets
            .iter()
            .fold(acc, |acc, (_, e, _)| mode_of_exp(e, modes, acc)),
        Exp::Case(disc, arms, _) => {
            let acc = mode_of_exp(disc, modes, acc);
            arms.iter()
                .fold(acc, |acc, (_, arm_e)| mode_of_exp(arm_e, modes, acc))
        }
        Exp::Con(_, _, Some(inner)) => mode_of_exp(inner, modes, acc),
        Exp::Some(_, inner) => mode_of_exp(inner, modes, acc),
        Exp::Error(inner, _)
        | Exp::Redirect(inner, _)
        | Exp::Uurlify(inner, _, _)
        | Exp::Recv(inner, _)
        | Exp::ServerCall(inner, _, _, _)
        | Exp::JavaScript(_, inner) => mode_of_exp(inner, modes, acc),
        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            let acc = if let Some(b) = blob {
                mode_of_exp(b, modes, acc)
            } else {
                acc
            };
            mode_of_exp(mime_type, modes, acc)
        }
        Exp::Closure(_, envs) => envs.iter().fold(acc, |acc, e| mode_of_exp(e, modes, acc)),
        // Leaves
        Exp::Prim(_) | Exp::Rel(_) | Exp::Ffi(_, _) | Exp::None(_) | Exp::Con(_, _, None) => acc,
    }
}

fn mode_of(e: &LocExp, modes: &HashMap<usize, DbMode>) -> DbMode {
    mode_of_exp(e, modes, DbMode::NoDb)
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Classify DB access mode for each declaration and update export metadata.
///
/// Mirrors `DbModeCheck.classify`.
pub fn classify(file: File) -> File {
    let (decls, mut ps) = file;

    // Build a map from named-val id → DbMode by scanning decls in order.
    let mut modes: HashMap<usize, DbMode> = HashMap::new();
    for d in &decls {
        match &d.node {
            Decl::Val(_, n, _, e, _) => {
                modes.insert(*n, mode_of(e, &modes));
            }
            Decl::ValRec(vis) => {
                // For mutually recursive groups: if any member accesses DB,
                // conservatively mark all as AnyDb.
                let group_mode = vis.iter().fold(DbMode::NoDb, |acc, (_, _, _, e, _)| {
                    let m = mode_of(e, &modes);
                    match m {
                        DbMode::NoDb => acc,
                        _ => DbMode::AnyDb,
                    }
                });
                for (_, n, _, _, _) in vis {
                    modes.insert(*n, group_mode);
                }
            }
            _ => {}
        }
    }

    // Update ps: assign computed mode to each export; remaining modes → ServerOnly.
    let mut remaining = modes.clone();
    ps = ps
        .into_iter()
        .map(|(n, side, _)| {
            let db_mode = remaining.remove(&n).unwrap_or(DbMode::AnyDb);
            (n, side, db_mode)
        })
        .collect();

    // Any named vals not already in ps: add as ServerOnly
    for (n, db_mode) in remaining {
        ps.push((n, Sidedness::ServerOnly, db_mode));
    }

    (decls, ps)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_file_classify() {
        let result = classify((vec![], vec![]));
        assert!(result.0.is_empty());
        assert!(result.1.is_empty());
    }

    #[test]
    fn merge_modes_no_db_is_identity() {
        assert_eq!(
            merge_modes(DbMode::NoDb, DbMode::OneQuery),
            DbMode::OneQuery
        );
        assert_eq!(
            merge_modes(DbMode::OneQuery, DbMode::NoDb),
            DbMode::OneQuery
        );
    }

    #[test]
    fn merge_modes_any_db_dominates() {
        assert_eq!(merge_modes(DbMode::AnyDb, DbMode::OneQuery), DbMode::AnyDb);
        assert_eq!(merge_modes(DbMode::OneQuery, DbMode::AnyDb), DbMode::AnyDb);
    }
}
