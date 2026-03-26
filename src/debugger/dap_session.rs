//! DAP request handling wired to [`super::gdb_session::GdbSession`].

use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::io::stdin;
use std::path::Path;
use std::sync::{Arc, Mutex};

use anyhow::{anyhow, Context, Result};
use serde_json::{json, Map, Value};

use super::dap_framing::{bump_seq, read_dap_message, write_dap_message};
use super::dap_shared::{DapState, LoadedSourceNotifier};
use super::gdb_session::{GdbSession, WatchAccess};
use super::mi_parse::{
    mi_extract_asm_insns, mi_extract_exec_source_file_paths, mi_extract_frames,
    mi_extract_shared_libraries, mi_extract_var_children, mi_get_str,
};

const FRAME_FACTOR: i64 = 100_000;
/// DAP `variablesReference` for expandable locals / MI var-objects (distinct from stack frame ids).
const VAR_REF_BASE: i64 = 50_000_000;

#[derive(Clone)]
struct LaunchConfig {
    program: String,
    args: Vec<String>,
    cwd: Option<String>,
    env: Vec<(String, String)>,
    gdb_path: String,
    /// `MIMode` / DAP-style: `gdb` (default) or `lldb` / `lldb-mi` (**lldb-mi** binary).
    mi_mode: String,
    stop_at_entry: bool,
    /// `-target-attach` when set.
    attach_pid: Option<u32>,
}

#[derive(Debug, Clone)]
enum VarRefKind {
    /// Local from `-stack-list-variables`; needs `-var-create` on first expand.
    PendingLocal {
        thread: u64,
        frame: u32,
        expr: String,
    },
    VarObj {
        thread: u64,
        frame: u32,
        varobj: String,
    },
}

struct Server {
    dap: Arc<Mutex<DapState>>,
    launch: Option<LaunchConfig>,
    /// Same effective DB as LSP/compiler when the workspace contains a unique `.urp` + `ur.toml`.
    resolved_project_db: Option<crate::db::ProjectDb>,
    gdb: Option<GdbSession>,
    /// Source path (client) → GDB breakpoint numbers to delete on refresh
    bkpt_by_source: HashMap<String, Vec<String>>,
    /// Breakpoints received before GDB starts (`setBreakpoints` before `configurationDone`).
    pending_by_source: HashMap<String, Vec<u32>>,
    next_bp_id: i64,
    /// First stopped event after launch should be reported as `entry` when `stopAtEntry` was set.
    expect_entry_stop: bool,
    /// DAP `setDataBreakpoints` before launch; applied in `finish_launch`.
    pending_watchpoints: Vec<(String, String)>,
    /// GDB `-break-watch` numbers for refresh / disconnect cleanup.
    watchpoint_nums: Vec<String>,
    /// `variablesReference` (≥ [`VAR_REF_BASE`]) → MI var-object state.
    var_refs: HashMap<i64, VarRefKind>,
    next_var_ref: i64,
    /// `setExceptionBreakpoints` before launch (`filter` ids).
    pending_exception_filters: Vec<String>,
    /// GDB numbers for `-catch-signal` / `-catch-throw` / `all`.
    catchpoint_nums: Vec<String>,
    /// Latest signal stop (for `exceptionInfo`).
    last_exception_description: Option<String>,
    last_exception_thread_id: Option<i64>,
    /// Paths already announced via `loadedSource` (shared with MI `=library-loaded` hook).
    known_loaded_sources: Arc<Mutex<HashSet<String>>>,
    /// `(canonical path, requested line)` → GDB-resolved `(line, addr)` for `breakpointLocations`.
    bp_loc_cache: HashMap<(String, u32), (u32, Option<String>)>,
    bp_loc_cache_order: VecDeque<(String, u32)>,
    /// GDB breakpoint numbers for `setInstructionBreakpoints` (`-break-insert *addr`).
    instruction_bp_nums: Vec<String>,
    /// Instruction addresses / DAP `instructionReference` strings before launch.
    pending_instruction_bps: Vec<String>,
}

impl Server {
    const BP_LOC_CACHE_MAX: usize = 4096;

    fn new(dap: Arc<Mutex<DapState>>, known_loaded_sources: Arc<Mutex<HashSet<String>>>) -> Self {
        Self {
            dap,
            launch: None,
            resolved_project_db: None,
            gdb: None,
            bkpt_by_source: HashMap::new(),
            pending_by_source: HashMap::new(),
            next_bp_id: 1,
            expect_entry_stop: false,
            pending_watchpoints: Vec::new(),
            watchpoint_nums: Vec::new(),
            var_refs: HashMap::new(),
            next_var_ref: VAR_REF_BASE,
            pending_exception_filters: Vec::new(),
            catchpoint_nums: Vec::new(),
            last_exception_description: None,
            last_exception_thread_id: None,
            known_loaded_sources,
            bp_loc_cache: HashMap::new(),
            bp_loc_cache_order: VecDeque::new(),
            instruction_bp_nums: Vec::new(),
            pending_instruction_bps: Vec::new(),
        }
    }

    fn bp_loc_cache_insert(&mut self, key: (String, u32), val: (u32, Option<String>)) {
        if self.bp_loc_cache.len() >= Self::BP_LOC_CACHE_MAX {
            if let Some(old) = self.bp_loc_cache_order.pop_front() {
                self.bp_loc_cache.remove(&old);
            }
        }
        if self.bp_loc_cache.insert(key.clone(), val).is_none() {
            self.bp_loc_cache_order.push_back(key);
        }
    }

    fn sync_loaded_sources(&mut self) -> Result<()> {
        let gdb = match self.gdb.as_mut() {
            Some(g) => g,
            None => return Ok(()),
        };
        let pl = gdb.file_list_exec_source_files().unwrap_or_default();
        let paths = mi_extract_exec_source_file_paths(&pl);
        let mut new_paths = Vec::new();
        {
            let mut known = self.known_loaded_sources.lock().unwrap();
            for p in paths {
                if known.insert(p.clone()) {
                    new_paths.push(p);
                }
            }
        }
        for p in new_paths {
            let mut st = self.dap.lock().unwrap();
            let body = json!({
                "reason": "new",
                "source": { "name": p, "path": p },
            });
            let msg = json!({
                "seq": bump_seq(&mut st.seq),
                "type": "event",
                "event": "loadedSource",
                "body": body,
            });
            write_dap_message(&mut st.out, &msg)?;
        }
        Ok(())
    }

    fn apply_instruction_breakpoints(
        &mut self,
        gdb: &mut GdbSession,
        addrs: &[String],
    ) -> Result<()> {
        for n in std::mem::take(&mut self.instruction_bp_nums) {
            gdb.break_delete(&n).ok();
        }
        for a in addrs {
            if a.is_empty() {
                continue;
            }
            if let Ok(Some(n)) = gdb.break_insert_at_address(a) {
                self.instruction_bp_nums.push(n);
            }
        }
        Ok(())
    }

    /// Probes use one `-break-insert` per line; teardown is a single CLI `delete` (plus optional cache hits).
    const BREAKPOINT_LOC_PROBE_MAX: u32 = 128;

    /// GDB-backed locations when a session and `Source.path` exist; otherwise heuristic lines.
    fn breakpoint_locations_for_args(&mut self, args: &Value) -> Vec<Value> {
        let path = args
            .get("source")
            .and_then(|s| s.get("path"))
            .and_then(|p| p.as_str())
            .unwrap_or("");
        let line = args.get("line").and_then(|x| x.as_u64()).unwrap_or(1) as u32;
        let end_line = args
            .get("endLine")
            .and_then(|x| x.as_u64())
            .map(|n| n as u32)
            .unwrap_or(line);
        let start = line.min(end_line);
        let end = line.max(end_line);
        let heuristic = || {
            (start..=end)
                .map(|ln| json!({ "line": ln, "column": 1 }))
                .collect::<Vec<_>>()
        };

        if path.is_empty() {
            return heuristic();
        }
        if end.saturating_sub(start).saturating_add(1) > Self::BREAKPOINT_LOC_PROBE_MAX {
            return heuristic();
        }
        let canon = Path::new(path)
            .canonicalize()
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_else(|_| path.to_string());

        let mut gdb = match self.gdb.take() {
            Some(g) => g,
            None => return heuristic(),
        };

        let mut out = Vec::new();
        let mut pending_delete: Vec<String> = Vec::new();
        for ln in start..=end {
            let key = (canon.clone(), ln);
            if let Some(&(bound, ref addr)) = self.bp_loc_cache.get(&key) {
                let mut m = Map::new();
                m.insert("line".into(), json!(bound));
                m.insert("column".into(), json!(1));
                if let Some(a) = addr {
                    m.insert("instructionReference".into(), json!(a));
                }
                out.push(Value::Object(m));
                continue;
            }
            match gdb.break_insert_probe_leave(&canon, ln) {
                Ok(Some((num, bound, addr))) => {
                    pending_delete.push(num);
                    let addr_for_cache = addr.clone();
                    self.bp_loc_cache_insert(key, (bound, addr_for_cache));
                    let mut m = Map::new();
                    m.insert("line".into(), json!(bound));
                    m.insert("column".into(), json!(1));
                    if let Some(a) = addr {
                        m.insert("instructionReference".into(), json!(a));
                    }
                    out.push(Value::Object(m));
                }
                Ok(None) | Err(_) => {
                    out.push(json!({ "line": ln, "column": 1 }));
                }
            }
        }
        let _ = gdb.break_delete_console_nums(&pending_delete);
        self.gdb = Some(gdb);
        out
    }

    fn apply_exception_filters(&mut self, gdb: &mut GdbSession, enabled: &[String]) -> Result<()> {
        for n in &self.catchpoint_nums {
            gdb.break_delete(n).ok();
        }
        self.catchpoint_nums.clear();
        for f in enabled {
            match f.as_str() {
                "fatal-signals" => {
                    for sig in [
                        "SIGSEGV", "SIGABRT", "SIGBUS", "SIGILL", "SIGFPE", "SIGTRAP",
                    ] {
                        if let Ok(Some(num)) = gdb.catch_signal(sig) {
                            self.catchpoint_nums.push(num);
                        }
                    }
                }
                "all-signals" => {
                    if let Ok(Some(num)) = gdb.catch_signal_all() {
                        self.catchpoint_nums.push(num);
                    }
                }
                "cpp-throw" => {
                    if let Ok(Some(num)) = gdb.catch_cpp_throw() {
                        self.catchpoint_nums.push(num);
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn alloc_var_ref(&mut self, kind: VarRefKind) -> i64 {
        let id = self.next_var_ref;
        self.next_var_ref += 1;
        self.var_refs.insert(id, kind);
        id
    }

    fn resolve_pending_var_obj(&mut self, gdb: &mut GdbSession, ref_id: i64) -> Result<VarRefKind> {
        let kind = self
            .var_refs
            .get(&ref_id)
            .cloned()
            .ok_or_else(|| anyhow!("stale variables reference"))?;
        match kind {
            VarRefKind::PendingLocal {
                thread,
                frame,
                expr,
            } => {
                let pl = gdb.var_create(thread, frame, &expr)?;
                let vname = mi_get_str(&pl, "name")
                    .ok_or_else(|| anyhow!("-var-create failed"))?
                    .to_string();
                let resolved = VarRefKind::VarObj {
                    thread,
                    frame,
                    varobj: vname,
                };
                self.var_refs.insert(ref_id, resolved.clone());
                Ok(resolved)
            }
            VarRefKind::VarObj { .. } => Ok(kind),
        }
    }

    fn variables_for_var_ref(&mut self, gdb: &mut GdbSession, ref_id: i64) -> Result<Vec<Value>> {
        let resolved = self.resolve_pending_var_obj(gdb, ref_id)?;
        let VarRefKind::VarObj {
            thread,
            frame,
            varobj,
        } = resolved
        else {
            return Ok(vec![]);
        };
        gdb.thread_select(thread).ok();
        let pl = gdb.var_list_children(&varobj)?;
        let blob_sec = pl.find("children=[").map(|i| &pl[i..]).unwrap_or(&pl);
        let mut out = Vec::new();
        for c in mi_extract_var_children(blob_sec) {
            let exp = mi_get_str(&c, "exp").unwrap_or("");
            let name = if !exp.is_empty() {
                exp
            } else {
                mi_get_str(&c, "name").unwrap_or("?")
            };
            let val = mi_get_str(&c, "value").unwrap_or("");
            let ty = mi_get_str(&c, "type").unwrap_or("");
            let numchild = mi_get_str(&c, "numchild")
                .and_then(|s| s.parse::<u32>().ok())
                .unwrap_or(0);
            let dynamic = mi_get_str(&c, "dynamic") == Some("1");
            let vo = mi_get_str(&c, "name").unwrap_or("");
            let vref = if (numchild > 0 || dynamic) && !vo.is_empty() {
                self.alloc_var_ref(VarRefKind::VarObj {
                    thread,
                    frame,
                    varobj: vo.to_string(),
                })
            } else {
                0
            };
            out.push(json!({
                "name": name,
                "value": val,
                "type": ty,
                "variablesReference": vref,
            }));
        }
        Ok(out)
    }

    fn set_variable_in_var_tree(
        &mut self,
        gdb: &mut GdbSession,
        ref_id: i64,
        field: &str,
        value: &str,
    ) -> Result<()> {
        let resolved = self.resolve_pending_var_obj(gdb, ref_id)?;
        let VarRefKind::VarObj { thread, varobj, .. } = resolved else {
            return Err(anyhow!("not a variable container"));
        };
        gdb.thread_select(thread).ok();
        let pl = gdb.var_list_children(&varobj)?;
        let blob_sec = pl.find("children=[").map(|i| &pl[i..]).unwrap_or(&pl);
        for c in mi_extract_var_children(blob_sec) {
            let exp = mi_get_str(&c, "exp").unwrap_or("");
            let vo = mi_get_str(&c, "name").unwrap_or("");
            if exp == field || vo == field || vo.ends_with(&format!(".{field}")) {
                gdb.var_assign(vo, value)?;
                return Ok(());
            }
        }
        Err(anyhow!("field not found: {field}"))
    }

    fn send_response(
        &mut self,
        request_id: &Value,
        command: &str,
        success: bool,
        body: Option<Value>,
        message: Option<&str>,
    ) -> Result<()> {
        let mut st = self.dap.lock().unwrap();
        let mut m = Map::new();
        m.insert("seq".into(), json!(bump_seq(&mut st.seq)));
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
        write_dap_message(&mut st.out, &Value::Object(m))?;
        Ok(())
    }

    fn send_event(&mut self, event: &str, body: Value) -> Result<()> {
        let mut st = self.dap.lock().unwrap();
        let msg = json!({
            "seq": bump_seq(&mut st.seq),
            "type": "event",
            "event": event,
            "body": body,
        });
        write_dap_message(&mut st.out, &msg)?;
        Ok(())
    }

    fn stopped_event(&mut self, payload: &str) -> Result<()> {
        let reason_gdb = mi_get_str(payload, "reason");
        let tid = mi_get_str(payload, "thread-id")
            .and_then(|s| s.parse::<i64>().ok())
            .unwrap_or(1);
        let mut dap_reason = match reason_gdb {
            Some("breakpoint-hit") => "breakpoint",
            Some("end-stepping-range") => "step",
            Some("signal-received") => "exception",
            Some("exited-normally") | Some("exited-signalled") => "pause",
            Some("watchpoint-trigger") => "data breakpoint",
            _ => "pause",
        };
        if self.expect_entry_stop && dap_reason == "breakpoint" {
            dap_reason = "entry";
            self.expect_entry_stop = false;
        }
        let mut stopped_body = Map::new();
        stopped_body.insert("reason".into(), json!(dap_reason));
        stopped_body.insert("threadId".into(), json!(tid));
        stopped_body.insert("allThreadsStopped".into(), json!(true));
        if reason_gdb == Some("signal-received") {
            let sig = mi_get_str(payload, "signal-name").unwrap_or("unknown");
            let desc = format!("Signal {sig}");
            stopped_body.insert("description".into(), json!(desc));
            self.last_exception_description = Some(format!("Delivered signal {sig}"));
            self.last_exception_thread_id = Some(tid);
        } else {
            self.last_exception_description = None;
            self.last_exception_thread_id = None;
        }
        self.send_event("stopped", Value::Object(stopped_body))?;
        if matches!(
            reason_gdb,
            Some("exited-normally") | Some("exited-signalled")
        ) {
            let code = mi_get_str(payload, "exit-code")
                .and_then(|s| {
                    let s = s.strip_prefix("0x").unwrap_or(s);
                    i64::from_str_radix(s, 16).ok().or_else(|| s.parse().ok())
                })
                .unwrap_or(0);
            self.send_event("terminated", json!({ "exitCode": code }))?;
        }
        Ok(())
    }

    fn finish_launch(&mut self) -> Result<()> {
        self.known_loaded_sources.lock().unwrap().clear();
        let cfg = self
            .launch
            .clone()
            .ok_or_else(|| anyhow!("no launch/attach request before configurationDone"))?;
        let mut exe = cfg.gdb_path.clone();
        let mm = cfg.mi_mode.to_ascii_lowercase();
        if mm == "lldb" || mm == "lldb-mi" || mm == "lldbmi" {
            if exe.is_empty() || exe == "gdb" {
                exe = "lldb-mi".to_string();
            }
        } else if exe.is_empty() {
            exe = "gdb".to_string();
        }
        let notifier = Arc::new(LoadedSourceNotifier {
            dap: self.dap.clone(),
            known_paths: self.known_loaded_sources.clone(),
        });
        let mut gdb = GdbSession::spawn(&exe, &mm, Some(notifier))
            .context("spawn debugger (GDB or lldb-mi)")?;
        let _ = gdb.mi_simple("-gdb-set confirm off");
        let lldb_async = mm == "lldb" || mm == "lldb-mi" || mm == "lldbmi";
        let _ = gdb.set_mi_async(!lldb_async);
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

        let wp_specs = std::mem::take(&mut self.pending_watchpoints);
        for old in std::mem::take(&mut self.watchpoint_nums) {
            gdb.break_delete(&old).ok();
        }
        self.watchpoint_nums.clear();
        for (expr, acc) in &wp_specs {
            if expr.is_empty() {
                continue;
            }
            let wa = dap_access_to_watch(acc);
            if let Ok(Some(n)) = gdb.break_watch(expr, wa) {
                self.watchpoint_nums.push(n);
            }
        }

        let exc_filters = std::mem::take(&mut self.pending_exception_filters);
        self.apply_exception_filters(&mut gdb, &exc_filters)?;

        let iaddrs = std::mem::take(&mut self.pending_instruction_bps);
        self.apply_instruction_breakpoints(&mut gdb, &iaddrs)?;

        self.gdb = Some(gdb);

        if cfg.attach_pid.is_none() {
            self.expect_entry_stop = cfg.stop_at_entry;
            let stop = {
                let g = self.gdb.as_mut().unwrap();
                g.exec_run(&cfg.args).context("run inferior")?
            };
            self.stopped_event(&stop)?;
            self.sync_loaded_sources()?;
        } else {
            let pl = {
                let g = self.gdb.as_mut().unwrap();
                g.mi_simple("-thread-info").unwrap_or_default()
            };
            self.send_event(
                "stopped",
                json!({
                    "reason": "pause",
                    "threadId": mi_get_str(&pl, "id").and_then(|s| s.parse().ok()).unwrap_or(1i64),
                    "allThreadsStopped": true,
                }),
            )?;
            self.sync_loaded_sources()?;
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

    fn handle(&mut self, command: &str, args: &Value, req_id: &Value) -> Result<bool> {
        match command {
            "initialize" => {
                let caps = json!({
                    "capabilities": {
                        "supportsConfigurationDoneRequest": true,
                        "supportsTerminateRequest": true,
                        "supportsPauseRequest": true,
                        "supportsEvaluateForHovers": true,
                        "supportsSetVariable": true,
                        "supportsDisassembleRequest": true,
                        "supportsDataBreakpoints": true,
                        "supportsLoadedSourcesRequest": true,
                        "supportsExceptionInfoRequest": true,
                        "supportsSourceRequest": true,
                        "supportsBreakpointLocationsRequest": true,
                        "supportsInstructionBreakpoints": true,
                        "supportsModulesRequest": true,
                        "exceptionBreakpointFilters": [
                            {
                                "filter": "fatal-signals",
                                "label": "Fatal signals (SIGSEGV, SIGABRT, …)",
                                "default": false,
                            },
                            {
                                "filter": "all-signals",
                                "label": "Any signal (-catch-signal all)",
                                "default": false,
                            },
                            {
                                "filter": "cpp-throw",
                                "label": "C++ exceptions (-catch-throw)",
                                "default": false,
                            },
                        ],
                    }
                });
                self.send_response(req_id, command, true, Some(caps), None)?;
                self.send_event("initialized", json!({}))?;
                Ok(true)
            }
            "launch" | "attach" => {
                let def = LaunchConfig {
                    program: String::new(),
                    args: vec![],
                    cwd: None,
                    env: vec![],
                    gdb_path: "gdb".to_string(),
                    mi_mode: "gdb".to_string(),
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
                    if let Some(g) = a.get("miDebuggerPath").and_then(|x| x.as_str()) {
                        lc.gdb_path = g.to_string();
                    }
                    if let Some(m) = a
                        .get("MIMode")
                        .or_else(|| a.get("miMode"))
                        .and_then(|x| x.as_str())
                    {
                        lc.mi_mode = m.to_string();
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
                        req_id,
                        command,
                        false,
                        None,
                        Some("launch requires program"),
                    )?;
                    return Ok(true);
                }
                let cwd = lc
                    .cwd
                    .as_deref()
                    .map(std::path::Path::new)
                    .map(std::path::Path::to_path_buf)
                    .or_else(|| {
                        std::path::Path::new(&lc.program)
                            .parent()
                            .map(|p| p.to_path_buf())
                    })
                    .unwrap_or_else(|| std::env::current_dir().unwrap_or_default());
                self.resolved_project_db =
                    crate::compiler::effective_project_db_for_workspace_root(&cwd).ok();
                self.launch = Some(lc);
                self.send_response(req_id, command, true, None, None)?;
                Ok(true)
            }
            "configurationDone" => {
                self.send_response(req_id, command, true, None, None)?;
                if self.launch.is_some() && self.gdb.is_none() {
                    self.finish_launch()?;
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
                    req_id,
                    command,
                    true,
                    Some(json!({ "breakpoints": bp })),
                    None,
                )?;
                Ok(true)
            }
            "breakpointLocations" => {
                let breakpoints = self.breakpoint_locations_for_args(args);
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({ "breakpoints": breakpoints })),
                    None,
                )?;
                Ok(true)
            }
            "setExceptionBreakpoints" => {
                let filters: Vec<String> = args
                    .get("filters")
                    .and_then(|x| x.as_array())
                    .map(|a| {
                        a.iter()
                            .filter_map(|v| v.as_str().map(String::from))
                            .collect()
                    })
                    .unwrap_or_default();
                if self.gdb.is_none() {
                    self.pending_exception_filters = filters;
                } else {
                    let mut gdb = self
                        .gdb
                        .take()
                        .ok_or_else(|| anyhow!("setExceptionBreakpoints: gdb session missing"))?;
                    let apply = self.apply_exception_filters(&mut gdb, &filters);
                    self.gdb = Some(gdb);
                    apply?;
                }
                self.send_response(req_id, command, true, None, None)?;
                Ok(true)
            }
            "setFunctionBreakpoints" => {
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({ "breakpoints": [] })),
                    None,
                )?;
                Ok(true)
            }
            "setDataBreakpoints" => {
                let specs: Vec<(String, String)> = args
                    .get("breakpoints")
                    .and_then(|b| b.as_array())
                    .map(|a| {
                        a.iter()
                            .filter_map(|bp| {
                                let expr = bp
                                    .get("dataId")
                                    .or_else(|| bp.get("expression"))
                                    .and_then(|x| x.as_str())?
                                    .trim();
                                if expr.is_empty() {
                                    return None;
                                }
                                let acc = bp
                                    .get("accessType")
                                    .and_then(|x| x.as_str())
                                    .unwrap_or("write")
                                    .to_string();
                                Some((expr.to_string(), acc))
                            })
                            .collect()
                    })
                    .unwrap_or_default();

                if self.gdb.is_none() {
                    self.pending_watchpoints = specs.clone();
                    let bp: Vec<Value> = specs
                        .iter()
                        .enumerate()
                        .map(|(i, (e, _))| {
                            json!({
                                "id": (i as i64) + 1,
                                "description": e,
                                "verified": false,
                            })
                        })
                        .collect();
                    self.send_response(
                        req_id,
                        command,
                        true,
                        Some(json!({ "breakpoints": bp })),
                        None,
                    )?;
                    return Ok(true);
                }
                let gdb = self.gdb.as_mut().unwrap();
                for n in &self.watchpoint_nums {
                    gdb.break_delete(n).ok();
                }
                self.watchpoint_nums.clear();
                for (expr, acc) in &specs {
                    if expr.is_empty() {
                        continue;
                    }
                    let wa = dap_access_to_watch(acc);
                    if let Ok(Some(n)) = gdb.break_watch(expr, wa) {
                        self.watchpoint_nums.push(n);
                    }
                }
                let bp: Vec<Value> = specs
                    .iter()
                    .enumerate()
                    .map(|(i, (e, _))| {
                        json!({
                            "id": (i as i64) + 1,
                            "description": e,
                            "verified": true,
                        })
                    })
                    .collect();
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({ "breakpoints": bp })),
                    None,
                )?;
                Ok(true)
            }
            "setInstructionBreakpoints" => {
                let addrs: Vec<String> = args
                    .get("breakpoints")
                    .and_then(|b| b.as_array())
                    .map(|a| {
                        a.iter()
                            .filter_map(|bp| {
                                bp.get("instructionReference")
                                    .or_else(|| bp.get("instructionreference"))
                                    .and_then(|x| x.as_str())
                                    .map(|s| s.trim().to_string())
                                    .filter(|s| !s.is_empty())
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                if self.gdb.is_none() {
                    let bp: Vec<Value> = addrs
                        .iter()
                        .enumerate()
                        .map(|(i, r)| {
                            json!({
                                "id": (i as i64) + 1,
                                "instructionReference": r,
                                "verified": false,
                            })
                        })
                        .collect();
                    self.pending_instruction_bps = addrs;
                    self.send_response(
                        req_id,
                        command,
                        true,
                        Some(json!({ "breakpoints": bp })),
                        None,
                    )?;
                    return Ok(true);
                }
                let mut gdb = self
                    .gdb
                    .take()
                    .ok_or_else(|| anyhow!("setInstructionBreakpoints: gdb session missing"))?;
                let apply = self.apply_instruction_breakpoints(&mut gdb, &addrs);
                self.gdb = Some(gdb);
                apply?;
                let bp: Vec<Value> = addrs
                    .iter()
                    .enumerate()
                    .map(|(i, r)| {
                        json!({
                            "id": (i as i64) + 1,
                            "instructionReference": r,
                            "verified": true,
                        })
                    })
                    .collect();
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({ "breakpoints": bp })),
                    None,
                )?;
                Ok(true)
            }
            "pause" => {
                let stop = {
                    let gdb = self
                        .gdb
                        .as_mut()
                        .ok_or_else(|| anyhow!("pause before launch"))?;
                    if let Some(t) = args.get("threadId").and_then(|x| x.as_u64()) {
                        gdb.thread_select(t).ok();
                    }
                    gdb.exec_interrupt()?
                };
                self.send_response(req_id, command, true, None, None)?;
                self.stopped_event(&stop)?;
                self.sync_loaded_sources()?;
                Ok(true)
            }
            "evaluate" => {
                let gdb = self
                    .gdb
                    .as_mut()
                    .ok_or_else(|| anyhow!("evaluate before launch"))?;
                let expr = args
                    .get("expression")
                    .and_then(|x| x.as_str())
                    .unwrap_or("");
                let frame_id = args.get("frameId").and_then(|x| x.as_i64());
                let thread = args
                    .get("threadId")
                    .and_then(|x| x.as_u64())
                    .or_else(|| frame_id.map(|fid| (fid.div_euclid(FRAME_FACTOR)).max(1) as u64))
                    .unwrap_or(1);
                let frame = frame_id
                    .map(|fid| fid.rem_euclid(FRAME_FACTOR) as u32)
                    .unwrap_or(0);
                let pl = gdb
                    .data_evaluate_expression(thread, frame, expr)
                    .unwrap_or_default();
                let value = mi_get_str(&pl, "value").unwrap_or("").to_string();
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({
                        "result": value,
                        "variablesReference": 0,
                    })),
                    None,
                )?;
                Ok(true)
            }
            "continue" => {
                let stop = {
                    let gdb = self
                        .gdb
                        .as_mut()
                        .ok_or_else(|| anyhow!("continue before launch"))?;
                    if let Some(t) = args.get("threadId").and_then(|x| x.as_u64()) {
                        gdb.thread_select(t).ok();
                    }
                    gdb.exec_continue()?
                };
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({ "allThreadsContinued": true })),
                    None,
                )?;
                self.stopped_event(&stop)?;
                self.sync_loaded_sources()?;
                Ok(true)
            }
            "next" => {
                let stop = {
                    let gdb = self
                        .gdb
                        .as_mut()
                        .ok_or_else(|| anyhow!("next before launch"))?;
                    thread_id_select(gdb, args);
                    gdb.exec_next()?
                };
                self.send_response(req_id, command, true, None, None)?;
                self.stopped_event(&stop)?;
                self.sync_loaded_sources()?;
                Ok(true)
            }
            "stepIn" => {
                let stop = {
                    let gdb = self
                        .gdb
                        .as_mut()
                        .ok_or_else(|| anyhow!("stepIn before launch"))?;
                    thread_id_select(gdb, args);
                    gdb.exec_step()?
                };
                self.send_response(req_id, command, true, None, None)?;
                self.stopped_event(&stop)?;
                self.sync_loaded_sources()?;
                Ok(true)
            }
            "stepOut" => {
                let stop = {
                    let gdb = self
                        .gdb
                        .as_mut()
                        .ok_or_else(|| anyhow!("stepOut before launch"))?;
                    thread_id_select(gdb, args);
                    gdb.exec_finish()?
                };
                self.send_response(req_id, command, true, None, None)?;
                self.stopped_event(&stop)?;
                self.sync_loaded_sources()?;
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
                    req_id,
                    command,
                    true,
                    Some(json!({ "scopes": scopes })),
                    None,
                )?;
                Ok(true)
            }
            "variables" => {
                let mut gdb = self
                    .gdb
                    .take()
                    .ok_or_else(|| anyhow!("variables before launch"))?;
                let ref_id = args.get("variablesReference").map(ref_as_i64).unwrap_or(0);
                let vars = if ref_id >= VAR_REF_BASE {
                    self.variables_for_var_ref(&mut gdb, ref_id)?
                } else {
                    let thread = (ref_id / FRAME_FACTOR).max(1) as u64;
                    let frame = (ref_id % FRAME_FACTOR) as u32;
                    gdb.thread_select(thread).ok();
                    let pl = gdb.stack_list_vars_all(thread, frame).unwrap_or_default();
                    build_stack_scope_variables(&pl, thread, frame, self)
                };
                self.gdb = Some(gdb);
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({ "variables": vars })),
                    None,
                )?;
                Ok(true)
            }
            "setVariable" => {
                let mut gdb = self
                    .gdb
                    .take()
                    .ok_or_else(|| anyhow!("setVariable before launch"))?;
                let ref_id = args.get("variablesReference").map(ref_as_i64).unwrap_or(0);
                let name = args.get("name").and_then(|x| x.as_str()).unwrap_or("");
                let value = args.get("value").and_then(|x| x.as_str()).unwrap_or("");
                if ref_id >= VAR_REF_BASE {
                    self.set_variable_in_var_tree(&mut gdb, ref_id, name, value)?;
                } else {
                    let thread = ref_id.div_euclid(FRAME_FACTOR).max(1) as u64;
                    let frame = ref_id.rem_euclid(FRAME_FACTOR) as u32;
                    gdb.set_variable(thread, frame, name, value)?;
                }
                self.gdb = Some(gdb);
                self.send_response(req_id, command, true, Some(json!({ "value": value })), None)?;
                Ok(true)
            }
            "loadedSources" => {
                let gdb = self
                    .gdb
                    .as_mut()
                    .ok_or_else(|| anyhow!("loadedSources before launch"))?;
                let pl = gdb.file_list_exec_source_files().unwrap_or_default();
                let paths = mi_extract_exec_source_file_paths(&pl);
                let sources: Vec<Value> = paths
                    .into_iter()
                    .map(|p| json!({ "name": p, "path": p }))
                    .collect();
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({ "sources": sources })),
                    None,
                )?;
                Ok(true)
            }
            "modules" => {
                let gdb = self
                    .gdb
                    .as_mut()
                    .ok_or_else(|| anyhow!("modules before launch"))?;
                let pl = gdb.file_list_shared_libraries().unwrap_or_default();
                let mut rows = mi_extract_shared_libraries(&pl);
                if let Some(lc) = self.launch.as_ref() {
                    let exe = lc.program.trim();
                    if !exe.is_empty() {
                        let canon = Path::new(exe)
                            .canonicalize()
                            .map(|p| p.to_string_lossy().into_owned())
                            .unwrap_or_else(|_| exe.to_string());
                        if !rows.iter().any(|(_, p)| p == &canon) {
                            rows.insert(0, ("executable".to_string(), canon));
                        }
                    }
                }
                let modules: Vec<Value> = rows
                    .into_iter()
                    .enumerate()
                    .map(|(i, (_id, p))| {
                        let name = Path::new(&p)
                            .file_name()
                            .and_then(|n| n.to_str())
                            .unwrap_or(p.as_str());
                        json!({
                            "id": (i as i64) + 1,
                            "name": name,
                            "path": p,
                            "isOptimized": false,
                        })
                    })
                    .collect();
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({ "modules": modules })),
                    None,
                )?;
                Ok(true)
            }
            "source" => {
                let path = args
                    .get("source")
                    .and_then(|s| s.get("path"))
                    .and_then(|p| p.as_str())
                    .unwrap_or("");
                if path.is_empty() {
                    self.send_response(
                        req_id,
                        command,
                        false,
                        None,
                        Some("source requires Source.path (sourceReference not supported)"),
                    )?;
                    return Ok(true);
                }
                let content = fs::read_to_string(path).map_err(|e| anyhow!("{e}"))?;
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({
                        "content": content,
                        "mimeType": "text/plain",
                    })),
                    None,
                )?;
                Ok(true)
            }
            "exceptionInfo" => {
                let req_tid = args.get("threadId").map(ref_as_i64);
                let desc = match (req_tid, self.last_exception_thread_id) {
                    (Some(t), Some(lt)) if t != lt => {
                        "No signal details for this thread.".to_string()
                    }
                    _ => self
                        .last_exception_description
                        .clone()
                        .unwrap_or_else(|| "No exception or signal information.".to_string()),
                };
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({
                        "exceptionId": "signal",
                        "description": desc,
                        "breakMode": "always",
                    })),
                    None,
                )?;
                Ok(true)
            }
            "disassemble" => {
                let gdb = self
                    .gdb
                    .as_mut()
                    .ok_or_else(|| anyhow!("disassemble before launch"))?;
                let mem = args
                    .get("memoryReference")
                    .and_then(|x| x.as_str())
                    .unwrap_or("");
                let start = dap_memory_ref_to_addr(mem).ok_or_else(|| {
                    anyhow!("disassemble requires memoryReference (hex address, e.g. from stackTrace.instructionPointerReference)")
                })?;
                let offset = args
                    .get("instructionOffset")
                    .and_then(|x| x.as_i64())
                    .unwrap_or(0);
                let count = args
                    .get("instructionCount")
                    .and_then(|x| x.as_u64())
                    .unwrap_or(48);
                let start_i = (start as i128).saturating_add(offset as i128).max(0) as u64;
                let end_i = start_i.saturating_add(count.saturating_mul(32));
                let start_s = format!("{start_i:#x}");
                let end_s = format!("{end_i:#x}");
                let pl = gdb
                    .data_disassemble_range(&start_s, &end_s)
                    .unwrap_or_default();
                let blob = pl.find("asm_insns=[").map(|i| &pl[i..]).unwrap_or(&pl);
                let rows = mi_extract_asm_insns(blob);
                let mut instructions: Vec<Value> = Vec::new();
                for (addr, inst) in rows {
                    let mut m = Map::new();
                    m.insert("address".into(), json!(addr));
                    m.insert("instruction".into(), json!(inst));
                    instructions.push(Value::Object(m));
                }
                self.send_response(
                    req_id,
                    command,
                    true,
                    Some(json!({ "instructions": instructions })),
                    None,
                )?;
                Ok(true)
            }
            "disconnect" | "terminate" => {
                if let Some(mut gdb) = self.gdb.take() {
                    for (_, k) in std::mem::take(&mut self.var_refs) {
                        if let VarRefKind::VarObj { varobj, .. } = k {
                            gdb.var_delete(&varobj).ok();
                        }
                    }
                    self.next_var_ref = VAR_REF_BASE;
                    for n in std::mem::take(&mut self.catchpoint_nums) {
                        gdb.break_delete(&n).ok();
                    }
                    for n in std::mem::take(&mut self.instruction_bp_nums) {
                        gdb.break_delete(&n).ok();
                    }
                    self.known_loaded_sources.lock().unwrap().clear();
                    gdb.gdb_exit().ok();
                    gdb.kill().ok();
                }
                self.send_response(req_id, command, true, None, None)?;
                Ok(false)
            }
            "shutdown" => {
                self.send_response(req_id, command, true, None, None)?;
                Ok(false)
            }
            _ => {
                self.send_response(req_id, command, true, None, None)?;
                Ok(true)
            }
        }
    }
}

fn dap_access_to_watch(s: &str) -> WatchAccess {
    match s {
        "read" => WatchAccess::Read,
        "readWrite" => WatchAccess::ReadWrite,
        _ => WatchAccess::Write,
    }
}

fn build_stack_scope_variables(pl: &str, thread: u64, frame: u32, srv: &mut Server) -> Vec<Value> {
    let mut out = Vec::new();
    let needle = "variables=[";
    let rest = match pl.find(needle) {
        Some(i) => &pl[i + needle.len()..],
        None => return out,
    };
    let end = rest.find(']').unwrap_or(rest.len());
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
            let numchild = mi_get_str(blob, "numchild")
                .and_then(|s| s.parse::<u32>().ok())
                .unwrap_or(0);
            let dynamic = mi_get_str(blob, "dynamic") == Some("1");
            let vref = if (numchild > 0 || dynamic) && !name.is_empty() {
                srv.alloc_var_ref(VarRefKind::PendingLocal {
                    thread,
                    frame,
                    expr: name.to_string(),
                })
            } else {
                0
            };
            out.push(json!({
                "name": name,
                "value": val,
                "type": ty,
                "variablesReference": vref,
            }));
        }
        idx = brace_start + close_rel + 1;
    }
    out
}

fn ref_as_i64(v: &Value) -> i64 {
    v.as_i64()
        .or_else(|| v.as_u64().map(|u| u as i64))
        .unwrap_or(0)
}

/// Parse DAP `memoryReference` / instruction pointer string into a numeric address.
fn dap_memory_ref_to_addr(s: &str) -> Option<u64> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    if let Some(rest) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        return u64::from_str_radix(rest, 16).ok();
    }
    if s.chars().all(|c| c.is_ascii_hexdigit()) {
        return u64::from_str_radix(s, 16).ok();
    }
    None
}

fn thread_id_select(gdb: &mut GdbSession, args: &Value) {
    if let Some(t) = args.get("threadId").and_then(|x| x.as_u64()) {
        gdb.thread_select(t).ok();
    }
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
    let dap = Arc::new(Mutex::new(DapState {
        seq: 0,
        out: std::io::stdout(),
    }));
    let known = Arc::new(Mutex::new(HashSet::new()));
    let mut srv = Server::new(dap, known);
    let mut stdin = stdin().lock();
    run_dap_loop(&mut srv, &mut stdin)?;
    Ok(())
}

fn run_dap_loop(srv: &mut Server, stdin: &mut impl std::io::BufRead) -> Result<()> {
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
        let continue_loop = srv.handle(command, &args, &req_id)?;
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
    use std::collections::HashSet;

    #[test]
    fn parses_stack_vars_and_child_refs() {
        let pl = r#"variables=[{name="x",value="42",type="int"},{name="s",value="{}",type="S",numchild="2"}]"#;
        let dap = Arc::new(Mutex::new(DapState {
            seq: 0,
            out: std::io::stdout(),
        }));
        let known = Arc::new(Mutex::new(HashSet::new()));
        let mut srv = Server::new(dap, known);
        let v = build_stack_scope_variables(pl, 1, 0, &mut srv);
        assert_eq!(v.len(), 2);
        assert_eq!(
            v[0].get("variablesReference").and_then(|x| x.as_i64()),
            Some(0)
        );
        assert!(
            v[1].get("variablesReference")
                .and_then(|x| x.as_i64())
                .unwrap()
                >= super::VAR_REF_BASE
        );
    }

    #[test]
    fn memory_ref_hex() {
        assert_eq!(super::dap_memory_ref_to_addr("0x10ff"), Some(0x10ff));
        assert_eq!(super::dap_memory_ref_to_addr("10ff"), Some(0x10ff));
        assert_eq!(super::dap_memory_ref_to_addr(""), None);
    }
}
