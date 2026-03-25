//! DAP request handling wired to [`super::gdb_session::GdbSession`].

use std::collections::HashMap;
use std::io::{stdin, stdout, StdinLock, Write};
use std::path::Path;

use anyhow::{anyhow, Context, Result};
use serde_json::{json, Map, Value};

use super::dap_framing::{bump_seq, read_dap_message, write_dap_message};
use super::gdb_session::GdbSession;
use super::mi_parse::{mi_extract_frames, mi_get_str};

const FRAME_FACTOR: i64 = 100_000;

struct LaunchConfig {
    program: String,
    args: Vec<String>,
    cwd: Option<String>,
    env: Vec<(String, String)>,
    gdb_path: String,
    stop_at_entry: bool,
    /// `-target-attach` when set.
    attach_pid: Option<u32>,
}

struct Server {
    seq: i64,
    launch: Option<LaunchConfig>,
    gdb: Option<GdbSession>,
    /// Source path (client) → GDB breakpoint numbers to delete on refresh
    bkpt_by_source: HashMap<String, Vec<String>>,
    /// Breakpoints received before GDB starts (`setBreakpoints` before `configurationDone`).
    pending_by_source: HashMap<String, Vec<u32>>,
    next_bp_id: i64,
    /// Deferred until `configurationDone`
    configured: bool,
}

impl Server {
    fn new() -> Self {
        Self {
            seq: 0,
            launch: None,
            gdb: None,
            bkpt_by_source: HashMap::new(),
            pending_by_source: HashMap::new(),
            next_bp_id: 1,
            configured: false,
        }
    }

    fn send_response(
        &mut self,
        out: &mut impl Write,
        request_id: &Value,
        command: &str,
        success: bool,
        body: Option<Value>,
        message: Option<&str>,
    ) -> Result<()> {
        let mut m = Map::new();
        m.insert("seq".into(), json!(bump_seq(&mut self.seq)));
        m.insert("type".into(), json!("response"));
        m.insert("request_seq".into(), request_id.clone());
        m.insert("success".into(), json!(success));
        m.insert("command".into(), json!(command));
        if let Some(b) = body {
            m.insert("body".into(), b);
        }
        if let Some(msg) = message {
            if !success {
                m.insert("message".into(), json!(msg));
            }
        }
        write_dap_message(out, &Value::Object(m))?;
        Ok(())
    }

    fn send_event(&mut self, out: &mut impl Write, event: &str, body: Value) -> Result<()> {
        let msg = json!({
            "seq": bump_seq(&mut self.seq),
            "type": "event",
            "event": event,
            "body": body,
        });
        write_dap_message(out, &msg)?;
        Ok(())
    }

    fn stopped_event(&mut self, out: &mut impl Write, payload: &str) -> Result<()> {
        let reason_gdb = mi_get_str(payload, "reason");
        let tid = mi_get_str(payload, "thread-id")
            .and_then(|s| s.parse::<i64>().ok())
            .unwrap_or(1);
        let dap_reason = match reason_gdb {
            Some("breakpoint-hit") => "breakpoint",
            Some("end-stepping-range") => "step",
            Some("signal-received") => "exception",
            Some("exited-normally") | Some("exited-signalled") => "pause",
            Some("watchpoint-trigger") => "data breakpoint",
            _ => "pause",
        };
        self.send_event(
            out,
            "stopped",
            json!({
                "reason": dap_reason,
                "threadId": tid,
                "allThreadsStopped": true,
            }),
        )
    }

    fn finish_launch(&mut self, out: &mut impl Write) -> Result<()> {
        let cfg = self
            .launch
            .as_ref()
            .ok_or_else(|| anyhow!("no launch/attach request before configurationDone"))?;
        let gdb_path = cfg.gdb_path.clone();
        let mut gdb = GdbSession::spawn(&gdb_path).context("spawn GDB")?;
        let _ = gdb.set_mi_async(false);
        if let Some(pid) = cfg.attach_pid {
            gdb.target_attach(pid).context("attach")?;
        } else {
            gdb.file_exec_and_symbols(
                Path::new(&cfg.program)
                    .canonicalize()
                    .unwrap_or_else(|_| Path::new(&cfg.program).to_path_buf())
                    .to_string_lossy()
                    .as_ref(),
            )
            .context("loading executable symbols")?;
            if let Some(ref cwd) = cfg.cwd {
                gdb.environment_cd(cwd).ok();
            }
            for (k, v) in &cfg.env {
                gdb.environment_set(k, v).ok();
            }
            if cfg.stop_at_entry {
                gdb.mi_simple("-break-insert -f main").ok();
            }
        }

        let pending = std::mem::take(&mut self.pending_by_source);
        for (path, lines) in pending {
            if let Some(old) = self.bkpt_by_source.remove(&path) {
                for n in old {
                    gdb.break_delete(&n).ok();
                }
            }
            let mut nums = Vec::new();
            let canon = Path::new(&path)
                .canonicalize()
                .map(|p| p.to_string_lossy().into_owned())
                .unwrap_or_else(|_| path.clone());
            for ln in &lines {
                match gdb.break_insert(&canon, *ln) {
                    Ok(Some(n)) => nums.push(n),
                    Ok(None) | Err(_) => {}
                }
            }
            self.bkpt_by_source.insert(path, nums);
        }

        self.gdb = Some(gdb);
        let gdb = self.gdb.as_mut().unwrap();

        if cfg.attach_pid.is_none() {
            let stop = gdb.exec_run(&cfg.args).context("run inferior")?;
            self.stopped_event(out, &stop)?;
        } else {
            let pl = gdb.mi_simple("-thread-info").unwrap_or_default();
            self.send_event(
                out,
                "stopped",
                json!({
                    "reason": "pause",
                    "threadId": mi_get_str(&pl, "id").and_then(|s| s.parse().ok()).unwrap_or(1i64),
                    "allThreadsStopped": true,
                }),
            )?;
        }
        Ok(())
    }

    fn apply_breakpoints(&mut self, source_path: &str, lines: &[u32]) -> Result<Vec<Value>> {
        if self.gdb.is_none() {
            self.pending_by_source
                .insert(source_path.to_string(), lines.to_vec());
            let mut v = Vec::new();
            for ln in lines {
                let id = self.next_bp_id;
                self.next_bp_id += 1;
                v.push(json!({
                    "id": id,
                    "verified": false,
                    "message": "Breakpoint installs after configurationDone (native debug uses .c paths until CJR emits #line for .ur)",
                    "source": { "path": source_path },
                    "line": ln,
                }));
            }
            return Ok(v);
        }
        let gdb = self.gdb.as_mut().unwrap();
        if let Some(old) = self.bkpt_by_source.remove(source_path) {
            for n in old {
                gdb.break_delete(&n).ok();
            }
        }
        let mut nums = Vec::new();
        let mut out_bp = Vec::new();
        let canon = Path::new(source_path)
            .canonicalize()
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_else(|_| source_path.to_string());
        for ln in lines {
            let id = self.next_bp_id;
            self.next_bp_id += 1;
            match gdb.break_insert(&canon, *ln) {
                Ok(Some(n)) => {
                    nums.push(n.clone());
                    out_bp.push(json!({
                        "id": id,
                        "verified": true,
                        "source": { "path": source_path },
                        "line": ln,
                    }));
                }
                Ok(None) | Err(_) => {
                    out_bp.push(json!({
                        "id": id,
                        "verified": false,
                        "message": "GDB could not set breakpoint (use generated .c path or DWARF file; .ur needs #line in CJR)",
                        "source": { "path": source_path },
                        "line": ln,
                    }));
                }
            }
        }
        self.bkpt_by_source.insert(source_path.to_string(), nums);
        Ok(out_bp)
    }

    fn handle(
        &mut self,
        command: &str,
        args: &Value,
        req_id: &Value,
        out: &mut impl Write,
    ) -> Result<bool> {
        match command {
            "initialize" => {
                let caps = json!({
                    "capabilities": {
                        "supportsConfigurationDoneRequest": true,
                        "supportsTerminateRequest": true,
                        "supportsSetVariable": false,
                        "exceptionBreakpointFilters": [],
                    }
                });
                self.send_response(out, req_id, command, true, Some(caps), None)?;
                self.send_event(out, "initialized", json!({}))?;
                Ok(true)
            }
            "launch" | "attach" => {
                let def = LaunchConfig {
                    program: String::new(),
                    args: vec![],
                    cwd: None,
                    env: vec![],
                    gdb_path: "gdb".to_string(),
                    stop_at_entry: false,
                    attach_pid: None,
                };
                let mut lc = def;
                if let Some(a) = args.as_object() {
                    if let Some(p) = a.get("program").and_then(|x| x.as_str()) {
                        lc.program = p.to_string();
                    }
                    if let Some(arr) = a.get("args").and_then(|x| x.as_array()) {
                        lc.args = arr
                            .iter()
                            .filter_map(|v| v.as_str().map(String::from))
                            .collect();
                    }
                    if let Some(c) = a.get("cwd").and_then(|x| x.as_str()) {
                        lc.cwd = Some(c.to_string());
                    }
                    if let Some(e) = a.get("env").and_then(|x| x.as_array()) {
                        for pair in e {
                            let o = pair.as_object();
                            if let (Some(k), Some(v)) = (
                                o.and_then(|m| m.get("name")).and_then(|x| x.as_str()),
                                o.and_then(|m| m.get("value")).and_then(|x| x.as_str()),
                            ) {
                                lc.env.push((k.to_string(), v.to_string()));
                            }
                        }
                    }
                    if let Some(g) = a.get("gdbPath").and_then(|x| x.as_str()) {
                        lc.gdb_path = g.to_string();
                    }
                    if let Some(s) = a.get("stopAtEntry").and_then(|x| x.as_bool()) {
                        lc.stop_at_entry = s;
                    }
                    if let Some(pid) = a.get("processId").and_then(Value::as_u64) {
                        lc.attach_pid = Some(pid as u32);
                    }
                }
                if command == "attach" && lc.attach_pid.is_none() {
                    self.send_response(
                        out,
                        req_id,
                        command,
                        false,
                        None,
                        Some("attach requires processId"),
                    )?;
                    return Ok(true);
                }
                if command == "launch" && lc.program.is_empty() {
                    self.send_response(
                        out,
                        req_id,
                        command,
                        false,
                        None,
                        Some("launch requires program"),
                    )?;
                    return Ok(true);
                }
                self.launch = Some(lc);
                self.send_response(out, req_id, command, true, None, None)?;
                Ok(true)
            }
            "configurationDone" => {
                self.configured = true;
                self.send_response(out, req_id, command, true, None, None)?;
                if self.launch.is_some() && self.gdb.is_none() {
                    self.finish_launch(out)?;
                }
                Ok(true)
            }
            "setBreakpoints" => {
                let source_path = args
                    .get("source")
                    .and_then(|s| s.get("path"))
                    .and_then(|p| p.as_str())
                    .unwrap_or("");
                let lines: Vec<u32> = args
                    .get("breakpoints")
                    .and_then(|b| b.as_array())
                    .map(|a| {
                        a.iter()
                            .filter_map(|x| {
                                x.get("line").and_then(|l| l.as_u64()).map(|n| n as u32)
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                let bp = if source_path.is_empty() {
                    vec![]
                } else {
                    self.apply_breakpoints(source_path, &lines)?
                };
                self.send_response(
                    out,
                    req_id,
                    command,
                    true,
                    Some(json!({ "breakpoints": bp })),
                    None,
                )?;
                Ok(true)
            }
            "setExceptionBreakpoints" | "setFunctionBreakpoints" => {
                self.send_response(
                    out,
                    req_id,
                    command,
                    true,
                    Some(json!({ "breakpoints": [] })),
                    None,
                )?;
                Ok(true)
            }
            "continue" => {
                let gdb = self
                    .gdb
                    .as_mut()
                    .ok_or_else(|| anyhow!("continue before launch"))?;
                if let Some(t) = args.get("threadId").and_then(|x| x.as_u64()) {
                    gdb.thread_select(t).ok();
                }
                let stop = gdb.exec_continue()?;
                self.send_response(
                    out,
                    req_id,
                    command,
                    true,
                    Some(json!({ "allThreadsContinued": true })),
                    None,
                )?;
                self.stopped_event(out, &stop)?;
                Ok(true)
            }
            "next" => {
                let gdb = self
                    .gdb
                    .as_mut()
                    .ok_or_else(|| anyhow!("next before launch"))?;
                thread_id_select(gdb, args);
                let stop = gdb.exec_next()?;
                self.send_response(out, req_id, command, true, None, None)?;
                self.stopped_event(out, &stop)?;
                Ok(true)
            }
            "stepIn" => {
                let gdb = self
                    .gdb
                    .as_mut()
                    .ok_or_else(|| anyhow!("stepIn before launch"))?;
                thread_id_select(gdb, args);
                let stop = gdb.exec_step()?;
                self.send_response(out, req_id, command, true, None, None)?;
                self.stopped_event(out, &stop)?;
                Ok(true)
            }
            "stepOut" => {
                let gdb = self
                    .gdb
                    .as_mut()
                    .ok_or_else(|| anyhow!("stepOut before launch"))?;
                thread_id_select(gdb, args);
                let stop = gdb.exec_finish()?;
                self.send_response(out, req_id, command, true, None, None)?;
                self.stopped_event(out, &stop)?;
                Ok(true)
            }
            "threads" => {
                let gdb = self
                    .gdb
                    .as_mut()
                    .ok_or_else(|| anyhow!("threads before launch"))?;
                let pl = gdb.mi_simple("-thread-info").unwrap_or_default();
                let mut threads = vec![];
                for part in pl.split("id=\"").skip(1) {
                    if let Some(end) = part.find('"') {
                        if let Ok(id) = part[..end].parse::<i64>() {
                            threads.push(json!({ "id": id, "name": format!("Thread {id}") }));
                        }
                    }
                }
                if threads.is_empty() {
                    threads.push(json!({ "id": 1, "name": "Thread 1" }));
                }
                self.send_response(
                    out,
                    req_id,
                    command,
                    true,
                    Some(json!({ "threads": threads })),
                    None,
                )?;
                Ok(true)
            }
            "stackTrace" => {
                let gdb = self
                    .gdb
                    .as_mut()
                    .ok_or_else(|| anyhow!("stackTrace before launch"))?;
                let thread = args.get("threadId").and_then(|x| x.as_u64()).unwrap_or(1);
                let start = args.get("startFrame").and_then(|x| x.as_u64()).unwrap_or(0) as u32;
                let levels = args.get("levels").and_then(|x| x.as_u64()).unwrap_or(20) as u32;
                let high = start + levels.saturating_sub(1);
                gdb.thread_select(thread).ok();
                let pl = gdb
                    .stack_list_frames(thread, start, high)
                    .unwrap_or_default();
                let frames_blob = pl.find("stack=[").map(|i| &pl[i..]).unwrap_or(&pl);
                let raw_frames = mi_extract_frames(frames_blob);
                let mut stack_frames = vec![];
                for (i, blob) in raw_frames.into_iter().enumerate() {
                    let level = mi_get_str(&blob, "level")
                        .and_then(|s| s.parse::<u32>().ok())
                        .unwrap_or(start + i as u32);
                    let name = mi_get_str(&blob, "func").unwrap_or("??").to_string();
                    let file = mi_get_str(&blob, "file").map(str::to_string);
                    let line = mi_get_str(&blob, "line")
                        .and_then(|s| s.parse::<u64>().ok())
                        .map(|n| n as i64);
                    let addr = mi_get_str(&blob, "addr").unwrap_or("0x0").to_string();
                    let frame_id = thread as i64 * FRAME_FACTOR + level as i64;
                    let mut sf = Map::new();
                    sf.insert("id".into(), json!(frame_id));
                    sf.insert("name".into(), json!(name));
                    sf.insert("line".into(), json!(line.unwrap_or(0)));
                    sf.insert("column".into(), json!(0));
                    let mut src = Map::new();
                    if let Some(ref f) = file {
                        src.insert("path".into(), json!(f));
                        sf.insert("source".into(), Value::Object(src));
                    }
                    sf.insert("instructionPointerReference".into(), json!(addr));
                    stack_frames.push(Value::Object(sf));
                }
                self.send_response(
                    out,
                    req_id,
                    command,
                    true,
                    Some(json!({ "stackFrames": stack_frames })),
                    None,
                )?;
                Ok(true)
            }
            "scopes" => {
                let frame_id = args.get("frameId").and_then(|x| x.as_i64()).unwrap_or(0);
                let scopes = vec![json!({
                    "name": "Locals",
                    "presentationHint": "locals",
                    "variablesReference": frame_id,
                    "expensive": false,
                })];
                self.send_response(
                    out,
                    req_id,
                    command,
                    true,
                    Some(json!({ "scopes": scopes })),
                    None,
                )?;
                Ok(true)
            }
            "variables" => {
                let gdb = self
                    .gdb
                    .as_mut()
                    .ok_or_else(|| anyhow!("variables before launch"))?;
                let ref_id = args.get("variablesReference").map(ref_as_i64).unwrap_or(0);
                let thread = (ref_id / FRAME_FACTOR) as u64;
                let frame = (ref_id % FRAME_FACTOR) as u32;
                gdb.thread_select(thread).ok();
                let pl = gdb.stack_list_vars(thread, frame).unwrap_or_default();
                let vars = parse_stack_variables(&pl);
                self.send_response(
                    out,
                    req_id,
                    command,
                    true,
                    Some(json!({ "variables": vars })),
                    None,
                )?;
                Ok(true)
            }
            "disconnect" | "terminate" => {
                if let Some(mut gdb) = self.gdb.take() {
                    gdb.gdb_exit().ok();
                    gdb.kill().ok();
                }
                self.send_response(out, req_id, command, true, None, None)?;
                Ok(false)
            }
            "shutdown" => {
                self.send_response(out, req_id, command, true, None, None)?;
                Ok(false)
            }
            _ => {
                self.send_response(out, req_id, command, true, None, None)?;
                Ok(true)
            }
        }
    }
}

fn ref_as_i64(v: &Value) -> i64 {
    v.as_i64()
        .or_else(|| v.as_u64().map(|u| u as i64))
        .unwrap_or(0)
}

fn thread_id_select(gdb: &mut GdbSession, args: &Value) {
    if let Some(t) = args.get("threadId").and_then(|x| x.as_u64()) {
        gdb.thread_select(t).ok();
    }
}

/// Parse `variables=[{name="x",value="1",type="int"},...]` from MI payload.
fn parse_stack_variables(pl: &str) -> Vec<Value> {
    let mut out = Vec::new();
    let needle = "variables=[";
    let rest = match pl.find(needle) {
        Some(i) => &pl[i + needle.len()..],
        None => return out,
    };
    let end = rest.find(']').map(|j| j + 1).unwrap_or(rest.len());
    let slice = &rest[..end.min(rest.len())];
    let mut idx = 0usize;
    while let Some(pos) = slice[idx..].find("{name=\"") {
        let brace_start = idx + pos;
        let inner = &slice[brace_start..];
        let Some(close_rel) = brace_close_from_open(inner) else {
            break;
        };
        let blob = &inner[..=close_rel];
        if let Some(name) = mi_get_str(blob, "name") {
            let val = mi_get_str(blob, "value").unwrap_or("");
            let ty = mi_get_str(blob, "type").unwrap_or("");
            out.push(json!({
                "name": name,
                "value": val,
                "type": ty,
                "variablesReference": 0,
            }));
        }
        idx = brace_start + close_rel + 1;
    }
    out
}

fn brace_close_from_open(s: &str) -> Option<usize> {
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

pub fn run_dap_stdio() -> Result<()> {
    let mut stdin = stdin().lock();
    let mut out = stdout();
    let mut srv = Server::new();
    run_dap_loop(&mut srv, &mut stdin, &mut out)?;
    Ok(())
}

fn run_dap_loop(srv: &mut Server, stdin: &mut StdinLock<'_>, out: &mut impl Write) -> Result<()> {
    loop {
        let msg = match read_dap_message(stdin)? {
            None => break,
            Some(m) => m,
        };
        let msg_type = msg.get("type").and_then(|t| t.as_str());
        if msg_type != Some("request") {
            continue;
        }
        let command = msg.get("command").and_then(|c| c.as_str()).unwrap_or("");
        let req_id = msg.get("id").cloned().unwrap_or(Value::Null);
        let args = msg.get("arguments").cloned().unwrap_or(Value::Null);
        let continue_loop = srv.handle(command, &args, &req_id, out)?;
        if !continue_loop {
            break;
        }
    }
    if let Some(mut gdb) = srv.gdb.take() {
        gdb.kill().ok();
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_stack_vars() {
        let pl = r#"variables=[{name="x",value="42",type="int"},{name="y",value="0",type="int"}]"#;
        let v = parse_stack_variables(pl);
        assert_eq!(v.len(), 2);
    }
}
