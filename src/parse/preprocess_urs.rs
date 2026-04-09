//! Fuel-bounded `.urs` preprocessing: bracket bare `nm :: Kind ->` quantifiers after earlier rewrites.
//!
//! This module is split from [`super`] so `parse/mod.rs` stays readable; it still uses the parent’s
//! `pp_urs_*` macros and [`super::rewrite_datatype_constructors`] / [`super::rewrite_sgn_where`] /
//! [`super::rewrite_case_expressions`].

#[cfg(test)]
pub(super) static PREPROCESS_URS_FUEL_TEST_OVERRIDE: std::sync::Mutex<Option<usize>> =
    std::sync::Mutex::new(None);

/// Test hook: override preprocess fuel (see [`super::test_set_preprocess_urs_fuel_override`]).
#[cfg(test)]
pub(super) fn set_test_fuel_override(fuel: Option<usize>) {
    // acquire the mutex guard for the fuel override; a poisoned mutex is a programmer error
    *match PREPROCESS_URS_FUEL_TEST_OVERRIDE.lock() {
        Ok(g) => g,
        Err(e) => panic!("PREPROCESS_URS_FUEL_TEST_OVERRIDE mutex poisoned: {e}"),
    } = fuel;
}

/// Drop one unit of fuel; if exhausted, append `source_text[current_index..]` and return the buffer in `Err`.
fn burn_preprocess_fuel_unit(
    fuel_remaining: &mut usize,
    output_buffer: &mut String,
    source_text: &str,
    current_index: usize,
) -> Result<(), String> {
    match fuel_remaining.checked_sub(1) {
        Some(next_fuel) => {
            *fuel_remaining = next_fuel;
            Ok(())
        }
        None => {
            output_buffer.push_str(&source_text[current_index..]);
            Err(std::mem::take(output_buffer))
        }
    }
}

/// Charge sixteen fuel units per inner-loop step (legacy `burn_hot` macro).
fn burn_preprocess_fuel_hot_inner(
    fuel_remaining: &mut usize,
    output_buffer: &mut String,
    source_text: &str,
    current_index: usize,
) -> Result<(), String> {
    for _hot_repeat_index in 0..16 {
        burn_preprocess_fuel_unit(fuel_remaining, output_buffer, source_text, current_index)?;
    }
    Ok(())
}

/// Scan a balanced `{...}` or `(...)` region starting at `b[*i] == open_delim` (inclusive). Updates `*i` past the close.
///
/// If delimiters never balance, appends `src[*i..]` to `out` and returns the finished `String` for the caller to return.
fn scan_kind_atom_balanced_delims(
    b: &[u8],
    src: &str,
    i: &mut usize,
    n: usize,
    step_cap: usize,
    fuel: &mut usize,
    out: &mut String,
    open_delim: u8,
    close_delim: u8,
) -> Option<String> {
    let mut depth = 1usize;
    *i = (*i).saturating_add(1).min(n);
    for _ in 0..step_cap {
        if let Err(done) = burn_preprocess_fuel_hot_inner(fuel, out, src, *i) {
            return Some(done);
        }
        if b.get(*i).is_none() {
            break;
        }
        if matches!(depth, 0) {
            break;
        }
        let ib = *i;
        if b[*i] == open_delim {
            depth = depth.saturating_add(1);
        } else if b[*i] == close_delim {
            depth = depth.saturating_sub(1);
        }
        *i = (*i).saturating_add(1).min(n);
        if let Some(0) = (*i).checked_sub(ib) {
            break;
        }
    }
    if pp_urs_depth_nonzero!(depth) {
        out.push_str(&src[*i..]);
        Some(std::mem::take(out))
    } else {
        None
    }
}

/// Parse `:::` or `::` at `i` (rejecting `::::`). Updates `i` on success. Returns `None` if no colon token matched.
fn parse_double_or_triple_colon(b: &[u8], i: &mut usize, n: usize) -> Option<&'static str> {
    if let Some(s3) = (*i).checked_add(3).and_then(|end| b.get((*i)..end)) {
        if matches!(s3, b":::") {
            let fourth_colon = matches!(
                (*i).checked_add(3).and_then(|k| b.get(k)).copied(),
                Some(b':')
            );
            if !fourth_colon {
                *i = (*i).saturating_add(3).min(n);
                return Some(":::");
            }
        }
    }
    if let Some(s2) = (*i).checked_add(2).and_then(|end| b.get((*i)..end)) {
        if matches!(s2, b"::") {
            let third_colon = matches!(
                (*i).checked_add(2).and_then(|k| b.get(k)).copied(),
                Some(b':')
            );
            if !third_colon {
                *i = (*i).saturating_add(2).min(n);
                return Some("::");
            }
        }
    }
    None
}

/// Preprocess a `.urs` signature file: case rewrites, signature `where`, datatype tokens, then fuel-bounded pass.
///
/// # Arguments
///
/// * `src` — Raw `.urs` text.
///
/// # Returns
///
/// String ready for [`super::parse_urs`]’s lexer. If internal fuel exhausts, remainder is appended (see body).
pub fn preprocess_urs(source_text: &str) -> String {
    let rewritten = super::rewrite_case_expressions(&super::rewrite_sgn_where(
        &super::rewrite_datatype_constructors(source_text),
    ));
    let src: &str = &rewritten;
    const DECL_KEYWORDS: &[&str] = &[
        "con",
        "class",
        "type",
        "structure",
        "signature",
        "datatype",
        "val",
    ];

    let b = src.as_bytes();
    let n = b.len();
    let step_cap = n.saturating_add(1);
    const PP_URS_MAX_FUEL: usize = 120_000_000;
    let mut fuel = n
        .saturating_mul(1024)
        .saturating_add(65536)
        .min(PP_URS_MAX_FUEL);
    #[cfg(test)]
    {
        if let Ok(guard) = PREPROCESS_URS_FUEL_TEST_OVERRIDE.lock() {
            if let Some(f) = *guard {
                fuel = f;
            }
        }
    }
    let mut out = String::with_capacity(n + 128);
    let mut i = 0;
    let mut last_token = String::new();

    let emit_word = |out_buf: &mut String, last: &mut String, w: &str| {
        out_buf.push_str(w);
        last.clear();
        last.push_str(w);
    };

    for _ in 0..step_cap.saturating_add(1) {
        if b.get(i).is_none() {
            break;
        }
        let i_at_outer = i;
        if let Err(done) = burn_preprocess_fuel_unit(&mut fuel, &mut out, src, i) {
            return done;
        }
        'pp_step: {
            if matches!(b.get(i).copied(), Some(b'('))
                && matches!(i.checked_add(1).and_then(|j| b.get(j)).copied(), Some(b'*'))
            {
                out.push_str("(*");
                i = i.saturating_add(2).min(n);
                let mut depth = 1usize;
                for _ in 0..step_cap {
                    if let Err(done) = burn_preprocess_fuel_hot_inner(&mut fuel, &mut out, src, i) {
                        return done;
                    }
                    if b.get(i).is_none() {
                        break;
                    }
                    if matches!(depth, 0) {
                        break;
                    }
                    let ib = i;
                    if matches!(b.get(i).copied(), Some(b'(')) {
                        let nx = i.checked_add(1).and_then(|j| b.get(j)).copied();
                        if matches!(nx, Some(b'*')) {
                            out.push_str("(*");
                            i = i.saturating_add(2).min(n);
                            depth = depth.saturating_add(1);
                        } else {
                            out.push(b[i] as char);
                            i = i.saturating_add(1).min(n);
                        }
                    } else if matches!(b.get(i).copied(), Some(b'*')) {
                        let nx = i.checked_add(1).and_then(|j| b.get(j)).copied();
                        if matches!(nx, Some(b')')) {
                            out.push_str("*)");
                            i = i.saturating_add(2).min(n);
                            depth = depth.saturating_sub(1);
                        } else {
                            out.push(b[i] as char);
                            i = i.saturating_add(1).min(n);
                        }
                    } else {
                        out.push(b[i] as char);
                        i = i.saturating_add(1).min(n);
                    }
                    if let Some(0) = i.checked_sub(ib) {
                        break;
                    }
                }
                if pp_urs_depth_nonzero!(depth) {
                    out.push_str(&src[i..]);
                    return out;
                }
                break 'pp_step;
            }

            if matches!(b[i], b'"') {
                out.push('"');
                last_token.clear();
                last_token.push('"');
                i = i.saturating_add(1).min(n);
                for _ in 0..step_cap {
                    if let Err(done) = burn_preprocess_fuel_hot_inner(&mut fuel, &mut out, src, i) {
                        return done;
                    }
                    if b.get(i).is_none() {
                        break;
                    }
                    if matches!(b[i], b'"') {
                        break;
                    }
                    let ib = i;
                    if matches!(b[i], b'\\') {
                        if let Some(nb) = i.checked_add(1).and_then(|j| b.get(j)).copied() {
                            out.push(b[i] as char);
                            out.push(nb as char);
                            i = i.saturating_add(2).min(n);
                        } else {
                            out.push(b[i] as char);
                            i = i.saturating_add(1).min(n);
                        }
                    } else {
                        out.push(b[i] as char);
                        i = i.saturating_add(1).min(n);
                    }
                    if let Some(0) = i.checked_sub(ib) {
                        break;
                    }
                }
                if let Some(ch) = b.get(i).copied() {
                    if matches!(ch, b'"') {
                        out.push('"');
                        i = i.saturating_add(1).min(n);
                    } else {
                        out.push_str(&src[i..]);
                        return out;
                    }
                }
                break 'pp_step;
            }

            if pp_urs_is_ws!(b[i]) {
                out.push(b[i] as char);
                i = i.saturating_add(1).min(n);
                break 'pp_step;
            }

            let id_word_start = b[i].is_ascii_alphabetic() || b[i] == b'_';
            if id_word_start {
                let id_start = i;
                for _ in 0..step_cap {
                    if let Err(done) = burn_preprocess_fuel_hot_inner(&mut fuel, &mut out, src, i) {
                        return done;
                    }
                    if b.get(i).is_none() {
                        break;
                    }
                    if pp_urs_id_cont!(b[i]) {
                    } else {
                        break;
                    }
                    let ib = i;
                    i = i.saturating_add(1).min(n);
                    if let Some(0) = i.checked_sub(ib) {
                        break;
                    }
                }
                if let Some(ch) = b.get(i).copied() {
                    if pp_urs_id_cont!(ch) {
                        out.push_str(&src[i..]);
                        return out;
                    }
                }
                let ident = &src[id_start..i];
                let is_decl_name = DECL_KEYWORDS.contains(&last_token.as_str());
                last_token.clear();
                last_token.push_str(ident);
                let is_pseudo_token = matches!(
                    ident,
                    "sgn_where"
                        | "sgn_subwhere"
                        | "arm_sep"
                        | "case_bar"
                        | "case_end"
                        | "dt_con0"
                        | "dt_bar"
                        | "dt_done"
                        | "dtype_of"
                );
                if is_decl_name || is_pseudo_token {
                } else {
                    let allow_quant = b[id_start].is_ascii_lowercase() || b[id_start] == b'_';
                    if allow_quant {
                        let ws1 = i;
                        for _ in 0..step_cap {
                            if let Err(done) =
                                burn_preprocess_fuel_hot_inner(&mut fuel, &mut out, src, i)
                            {
                                return done;
                            }
                            if b.get(i).is_none() {
                                break;
                            }
                            if pp_urs_is_ws!(b[i]) {
                            } else {
                                break;
                            }
                            let ib = i;
                            i = i.saturating_add(1).min(n);
                            if let Some(0) = i.checked_sub(ib) {
                                break;
                            }
                        }
                        if let Some(ch) = b.get(i).copied() {
                            if pp_urs_is_ws!(ch) {
                                out.push_str(&src[i..]);
                                return out;
                            }
                        }
                        let colon_start = i;
                        let colons: &str = match parse_double_or_triple_colon(b, &mut i, n) {
                            Some(cs) => cs,
                            None => {
                                out.push_str(ident);
                                out.push_str(&src[ws1..i]);
                                break 'pp_step;
                            }
                        };

                        let ws2 = i;
                        for _ in 0..step_cap {
                            if let Err(done) =
                                burn_preprocess_fuel_hot_inner(&mut fuel, &mut out, src, i)
                            {
                                return done;
                            }
                            if b.get(i).is_none() {
                                break;
                            }
                            if pp_urs_is_ws!(b[i]) {
                            } else {
                                break;
                            }
                            let ib = i;
                            i = i.saturating_add(1).min(n);
                            if let Some(0) = i.checked_sub(ib) {
                                break;
                            }
                        }
                        if let Some(ch) = b.get(i).copied() {
                            if pp_urs_is_ws!(ch) {
                                out.push_str(&src[i..]);
                                return out;
                            }
                        }

                        let ka_start = i;
                        if b.get(i).is_some() {
                            if matches!(b[i], b'{') {
                                if let Some(done) = scan_kind_atom_balanced_delims(
                                    b, src, &mut i, n, step_cap, &mut fuel, &mut out, b'{', b'}',
                                ) {
                                    return done;
                                }
                            } else if matches!(b[i], b'(') {
                                if let Some(done) = scan_kind_atom_balanced_delims(
                                    b, src, &mut i, n, step_cap, &mut fuel, &mut out, b'(', b')',
                                ) {
                                    return done;
                                }
                            } else {
                                let kind_id = b[i].is_ascii_alphabetic() || b[i] == b'_';
                                if kind_id {
                                    for _ in 0..step_cap {
                                        if let Err(done) = burn_preprocess_fuel_hot_inner(
                                            &mut fuel, &mut out, src, i,
                                        ) {
                                            return done;
                                        }
                                        if b.get(i).is_none() {
                                            break;
                                        }
                                        if pp_urs_id_cont!(b[i]) {
                                        } else {
                                            break;
                                        }
                                        let ib = i;
                                        i = i.saturating_add(1).min(n);
                                        if let Some(0) = i.checked_sub(ib) {
                                            break;
                                        }
                                    }
                                    if let Some(ch) = b.get(i).copied() {
                                        if pp_urs_id_cont!(ch) {
                                            out.push_str(&src[i..]);
                                            return out;
                                        }
                                    }
                                } else {
                                    out.push_str(ident);
                                    out.push_str(&src[ws1..ws2]);
                                    out.push_str(colons);
                                    out.push_str(&src[ws2..i]);
                                    break 'pp_step;
                                }
                            }
                        } else {
                            out.push_str(ident);
                            out.push_str(&src[ws1..ws2]);
                            out.push_str(colons);
                            out.push_str(&src[ws2..i]);
                            break 'pp_step;
                        }
                        let kind_atom = &src[ka_start..i];

                        let ws3 = i;
                        for _ in 0..step_cap {
                            if let Err(done) =
                                burn_preprocess_fuel_hot_inner(&mut fuel, &mut out, src, i)
                            {
                                return done;
                            }
                            if b.get(i).is_none() {
                                break;
                            }
                            if pp_urs_is_ws!(b[i]) {
                            } else {
                                break;
                            }
                            let ib = i;
                            i = i.saturating_add(1).min(n);
                            if let Some(0) = i.checked_sub(ib) {
                                break;
                            }
                        }
                        if let Some(ch) = b.get(i).copied() {
                            if pp_urs_is_ws!(ch) {
                                out.push_str(&src[i..]);
                                return out;
                            }
                        }

                        let emit_without_arrow = |output_accumulator: &mut String| {
                            output_accumulator.push_str(ident);
                            output_accumulator.push_str(&src[ws1..colon_start]);
                            output_accumulator.push_str(colons);
                            output_accumulator.push_str(&src[ws2..ka_start]);
                            output_accumulator.push_str(kind_atom);
                            output_accumulator.push_str(&src[ws3..i]);
                        };
                        if let Some(nb) = i.checked_add(1).and_then(|j| b.get(j)).copied() {
                            if matches!(b.get(i).copied(), Some(b'-')) {
                                if matches!(nb, b'>') {
                                    out.push('[');
                                    out.push_str(ident);
                                    out.push(' ');
                                    out.push_str(colons);
                                    out.push(' ');
                                    out.push_str(kind_atom);
                                    out.push(']');
                                    out.push_str(&src[ws3..i]);
                                    last_token.clear();
                                    last_token.push(']');
                                } else {
                                    emit_without_arrow(&mut out);
                                }
                            } else {
                                emit_without_arrow(&mut out);
                            }
                        } else {
                            emit_without_arrow(&mut out);
                        }
                        break 'pp_step;
                    }
                }

                emit_word(&mut out, &mut last_token, ident);
                break 'pp_step;
            }

            out.push(b[i] as char);
            last_token.clear();
            last_token.push(b[i] as char);
            i = i.saturating_add(1).min(n);
        }
        if let Some(0) = i.checked_sub(i_at_outer) {
            out.push_str(src.get(i..).unwrap_or(""));
            return out;
        }
    }

    out.push_str(src.get(i..).unwrap_or(""));
    out
}
