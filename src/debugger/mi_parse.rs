//! GDB/MI line classification and light-weight result slicing.

/// GDB/MI result class after `^`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MiResultClass {
    Done,
    Running,
    Error,
    Connected,
    Exit,
}

/// A classified MI output line (single-line records only).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MiRecord<'a> {
    /// `token^class,payload` — `payload` is the part after `class` (may be empty or `,k=v...`).
    Result {
        token: u64,
        class: MiResultClass,
        payload: &'a str,
    },
    /// `*stopped,...` or `*running,...` etc.
    ExecAsync { class: &'a str, payload: &'a str },
    /// `=foobar,...`
    StatusAsync { class: &'a str, payload: &'a str },
    /// Console stream `~""` — ignored for control flow
    StreamConsole,
    /// Target stream `@""`
    StreamTarget,
    /// Log `&""`
    Log,
    /// `(gdb)` prompt
    Prompt,
}

pub fn classify_mi_line(line: &str) -> Option<MiRecord<'_>> {
    let line = line.trim_end();
    if line.is_empty() {
        return None;
    }
    if line == "(gdb)" {
        return Some(MiRecord::Prompt);
    }
    let bytes = line.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    let (token_opt, rest) = if i > 0
        && i < bytes.len()
        && matches!(bytes[i], b'^' | b'*' | b'=' | b'~' | b'@' | b'&')
    {
        let t: u64 = line[..i].parse().ok()?;
        (Some(t), &line[i..])
    } else {
        (None, line)
    };
    if let Some(r) = rest.strip_prefix('^') {
        let class = r.split(|c| c == ',' || c == '\n').next().unwrap_or("");
        let mi_class = match class {
            "done" => MiResultClass::Done,
            "running" => MiResultClass::Running,
            "error" => MiResultClass::Error,
            "connected" => MiResultClass::Connected,
            "exit" => MiResultClass::Exit,
            _ => MiResultClass::Done,
        };
        let payload = if let Some(pos) = r.find(',') {
            &r[pos + 1..]
        } else {
            ""
        };
        let tok = token_opt.unwrap_or(0);
        return Some(MiRecord::Result {
            token: tok,
            class: mi_class,
            payload,
        });
    }
    if let Some(r) = rest.strip_prefix('*') {
        let class = r.split(|c| c == ',' || c == '\n').next().unwrap_or("");
        let payload = if let Some(pos) = r.find(',') {
            &r[pos + 1..]
        } else {
            ""
        };
        return Some(MiRecord::ExecAsync { class, payload });
    }
    if let Some(r) = rest.strip_prefix('=') {
        let class = r.split(|c| c == ',' || c == '\n').next().unwrap_or("");
        let payload = if let Some(pos) = r.find(',') {
            &r[pos + 1..]
        } else {
            ""
        };
        return Some(MiRecord::StatusAsync { class, payload });
    }
    if rest.starts_with('~') || rest.starts_with('@') {
        return Some(if rest.starts_with('~') {
            MiRecord::StreamConsole
        } else {
            MiRecord::StreamTarget
        });
    }
    if rest.starts_with('&') {
        return Some(MiRecord::Log);
    }
    None
}

/// Find `key="value"` with simple quoted value (no escapes).
pub fn mi_get_str<'a>(payload: &'a str, key: &str) -> Option<&'a str> {
    let needle = format!("{key}=\"");
    let start = payload.find(&needle)?;
    let val_start = start + needle.len();
    let end = payload[val_start..].find('"')?;
    Some(&payload[val_start..val_start + end])
}

/// Extract each `frame={...}` block from GDB `-stack-list-frames` output slice.
pub fn mi_extract_frames(stack_list_payload: &str) -> Vec<String> {
    let mut v = Vec::new();
    let mut rest = stack_list_payload;
    while let Some(pos) = rest.find("frame={") {
        let from = pos + "frame=".len();
        let inner = &rest[from..];
        if let Some(end) = brace_close_index(inner) {
            v.push(inner[..=end].to_string());
            rest = &inner[end + 1..];
        } else {
            break;
        }
    }
    v
}

fn brace_close_index(s: &str) -> Option<usize> {
    if !s.starts_with('{') {
        return None;
    }
    let mut depth = 0i32;
    let mut in_quote = false;
    for (i, c) in s.char_indices() {
        match c {
            '"' => in_quote = !in_quote,
            '{' if !in_quote => depth += 1,
            '}' if !in_quote => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Rows of `(address, instruction_text)` from `-data-disassemble` `asm_insns=[...]`.
/// Each `child={...}` inside `-var-list-children` output.
pub fn mi_extract_var_children(children_payload: &str) -> Vec<String> {
    let mut v = Vec::new();
    let mut rest = children_payload;
    while let Some(pos) = rest.find("child={") {
        let from = pos + "child=".len();
        let inner = &rest[from..];
        if let Some(end) = brace_close_index(inner) {
            v.push(inner[..=end].to_string());
            rest = &inner[end + 1..];
        } else {
            break;
        }
    }
    v
}

pub fn mi_extract_asm_insns(payload: &str) -> Vec<(String, String)> {
    let mut v = Vec::new();
    let mut rest = payload;
    while let Some(pos) = rest.find("{address=\"") {
        let inner = &rest[pos..];
        if let Some(end) = brace_close_index(inner) {
            let blob = &inner[..=end];
            if let Some(addr) = mi_get_str(blob, "address") {
                let inst = mi_get_str(blob, "inst").unwrap_or("").to_string();
                v.push((addr.to_string(), inst));
            }
            rest = &inner[end + 1..];
        } else {
            break;
        }
    }
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_done_with_token() {
        match classify_mi_line("42^done,bkpt={number=\"1\"}") {
            Some(MiRecord::Result {
                token: 42,
                class: MiResultClass::Done,
                payload,
            }) => {
                assert!(payload.contains("bkpt="));
            }
            o => panic!("unexpected {o:?}"),
        }
    }

    #[test]
    fn classify_running() {
        match classify_mi_line("9^running") {
            Some(MiRecord::Result {
                token: 9,
                class: MiResultClass::Running,
                ..
            }) => {}
            o => panic!("unexpected {o:?}"),
        }
    }

    #[test]
    fn classify_stopped() {
        match classify_mi_line("*stopped,reason=\"breakpoint-hit\",thread-id=\"1\"") {
            Some(MiRecord::ExecAsync {
                class: "stopped",
                payload,
            }) => {
                assert_eq!(mi_get_str(payload, "reason"), Some("breakpoint-hit"));
            }
            o => panic!("unexpected {o:?}"),
        }
    }

    #[test]
    fn mi_get_str_finds_thread() {
        let p = "reason=\"end-stepping-range\",thread-id=\"2\",stopped-threads=\"all\"";
        assert_eq!(mi_get_str(p, "thread-id"), Some("2"));
    }

    #[test]
    fn extract_two_frames() {
        let s = r#"stack=[frame={level="0",addr="0x1",func="a",file="x.c",line="1"},frame={level="1",addr="0x2",func="b",file="y.c",line="2"}]"#;
        let frames = mi_extract_frames(s);
        assert_eq!(frames.len(), 2);
        assert!(frames[0].contains("func=\"a\""));
    }

    #[test]
    fn extract_asm_rows() {
        let p = r#"asm_insns=[{address="0x100",inst="push %rbp"},{address="0x101",inst="mov %rsp,%rbp"}]"#;
        let rows = mi_extract_asm_insns(p);
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].0, "0x100");
        assert_eq!(rows[0].1, "push %rbp");
    }

    #[test]
    fn extract_var_children() {
        let s = r#"numchild="2",children=[child={name="v.0",exp="x",value="1",type="int",numchild="0"},child={name="v.1",exp="y",value="2",type="int",numchild="0"}]"#;
        let ch = mi_extract_var_children(s);
        assert_eq!(ch.len(), 2);
        assert!(ch[0].contains("exp=\"x\""));
    }
}
