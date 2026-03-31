//! Spawn GDB in MI3 mode and exchange commands.

use std::collections::VecDeque;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

use anyhow::{anyhow, Result};

use super::diagnostic_locale::debugger_diagnostic_text;
use crate::diagnostics::DiagnosticId;

use super::dap_shared::LoadedSourceNotifier;
use super::mi_parse::{
    classify_mi_line, mi_break_insert_line_addr, mi_get_str, MiRecord, MiResultClass,
};

enum GdbLine {
    Line(String),
    Eof,
}

pub struct GdbSession {
    child: Child,
    stdin: ChildStdin,
    lines: Arc<Mutex<VecDeque<GdbLine>>>,
    line_cv: Arc<Condvar>,
    next_token: u64,
}

impl GdbSession {
    /// Run GDB (`--interpreter=mi3`) or LLDB via **lldb-mi** (`--interpreter=mi2`).
    /// Launch `MIMode`: `gdb` (default) or `lldb` / `lldb-mi`.
    pub fn spawn(
        exe: &str,
        mi_mode: &str,
        loaded_notifier: Option<Arc<LoadedSourceNotifier>>,
    ) -> Result<Self> {
        let mm = mi_mode.to_ascii_lowercase();
        let lldb = mm == "lldb" || mm == "lldb-mi" || mm == "lldbmi";
        let mut child = Command::new(exe);
        child
            .arg("-q")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        if lldb {
            child.args(["--interpreter", "mi2"]);
        } else {
            child.arg("--interpreter=mi3");
        }
        let mut child = child.spawn().map_err(|spawn_error| {
            anyhow!(
                "{}",
                debugger_diagnostic_text(
                    DiagnosticId::CliDebuggerSpawnMiBackendFailed,
                    vec![
                        exe.to_string(),
                        mi_mode.to_string(),
                        spawn_error.to_string(),
                    ],
                )
            )
        })?;
        let stdin = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        let stderr = child.stderr.take().unwrap();
        thread::spawn(move || {
            let mut br = BufReader::new(stderr);
            let mut line = String::new();
            while br.read_line(&mut line).unwrap_or(0) > 0 {
                eprint!("[ur-debugger mi] {line}");
                line.clear();
            }
        });
        let lines = Arc::new(Mutex::new(VecDeque::new()));
        let line_cv = Arc::new(Condvar::new());
        let lines_reader = lines.clone();
        let line_cv_reader = line_cv.clone();
        thread::spawn(move || {
            let mut br = BufReader::new(stdout);
            let mut line = String::new();
            while br.read_line(&mut line).unwrap_or(0) > 0 {
                let s = line.trim_end_matches(['\r', '\n']).to_string();
                line.clear();
                if s.is_empty() {
                    continue;
                }
                if let Some(ref n) = loaded_notifier {
                    let _ = n.on_mi_line(&s);
                }
                let mut q = lines_reader.lock().unwrap();
                q.push_back(GdbLine::Line(s));
                drop(q);
                line_cv_reader.notify_one();
            }
            let mut q = lines_reader.lock().unwrap();
            q.push_back(GdbLine::Eof);
            drop(q);
            line_cv_reader.notify_all();
        });
        Ok(Self {
            child,
            stdin,
            lines,
            line_cv,
            next_token: 1,
        })
    }

    fn read_line_raw(&mut self) -> Result<String> {
        let mut guard = self.lines.lock().unwrap();
        loop {
            match guard.pop_front() {
                Some(GdbLine::Line(l)) => {
                    if l.is_empty() {
                        continue;
                    }
                    return Ok(l);
                }
                Some(GdbLine::Eof) => {
                    return Err(anyhow!(
                        "{}",
                        debugger_diagnostic_text(DiagnosticId::CliDebuggerGdbStdoutClosed, vec![])
                    ));
                }
                None => {
                    guard = self.line_cv.wait(guard).map_err(|_| {
                        anyhow!(
                            "{}",
                            debugger_diagnostic_text(
                                DiagnosticId::CliDebuggerGdbLineQueueMutexPoisoned,
                                vec![]
                            )
                        )
                    })?;
                }
            }
        }
    }

    fn send_cmd(&mut self, cmd: &str) -> Result<u64> {
        let t = self.next_token;
        self.next_token += 1;
        let full = format!("{t}{cmd}\n");
        self.stdin.write_all(full.as_bytes())?;
        self.stdin.flush()?;
        Ok(t)
    }

    /// Non-execution MI command; completes at matching `^done` / `^error`.
    pub fn mi_simple(&mut self, cmd: &str) -> Result<String> {
        let t = self.send_cmd(cmd)?;
        self.drain_until_token_done(t)
    }

    fn drain_until_token_done(&mut self, token: u64) -> Result<String> {
        loop {
            let line = self.read_line_raw()?;
            if line.trim().is_empty() {
                continue;
            }
            match classify_mi_line(line.trim_end()) {
                Some(MiRecord::Result {
                    token: tok,
                    class: MiResultClass::Error,
                    payload: pl,
                }) if tok == token => {
                    let msg = mi_get_str(pl, "msg").unwrap_or("GDB/MI error");
                    return Err(anyhow!(
                        "{}",
                        debugger_diagnostic_text(
                            DiagnosticId::CliDebuggerGdbMiReported,
                            vec![msg.to_string()],
                        )
                    ));
                }
                Some(MiRecord::Result {
                    token: tok,
                    class: MiResultClass::Done,
                    payload: pl,
                }) if tok == token => {
                    return Ok(pl.to_string());
                }
                Some(MiRecord::Result {
                    token: tok,
                    class: MiResultClass::Connected,
                    payload: pl,
                }) if tok == token => {
                    return Ok(pl.to_string());
                }
                _ => {}
            }
        }
    }

    /// `-exec-*` style command: wait for `token^running` then `*stopped,...`.
    pub fn mi_exec_until_stop(&mut self, cmd: &str) -> Result<String> {
        let t = self.send_cmd(cmd)?;
        let mut running = false;
        loop {
            let line = self.read_line_raw()?;
            if line.trim().is_empty() {
                continue;
            }
            let tl = line.trim_end();
            match classify_mi_line(tl) {
                Some(MiRecord::Result {
                    token: tok,
                    class: MiResultClass::Running,
                    ..
                }) if tok == t => {
                    running = true;
                }
                Some(MiRecord::Result {
                    token: tok,
                    class: MiResultClass::Error,
                    payload: pl,
                }) if tok == t => {
                    let msg = mi_get_str(pl, "msg").unwrap_or("GDB/MI error");
                    return Err(anyhow!(
                        "{}",
                        debugger_diagnostic_text(
                            DiagnosticId::CliDebuggerGdbMiReported,
                            vec![msg.to_string()],
                        )
                    ));
                }
                Some(MiRecord::ExecAsync {
                    class: "running", ..
                }) => {
                    running = true;
                }
                Some(MiRecord::ExecAsync {
                    class: "stopped",
                    payload,
                }) if running => {
                    return Ok(payload.to_string());
                }
                _ => {}
            }
        }
    }

    pub fn file_exec_and_symbols(&mut self, program: &str) -> Result<()> {
        self.mi_simple(&format!("-file-exec-and-symbols {}", shell_escape(program)))?;
        Ok(())
    }

    pub fn set_mi_async(&mut self, on: bool) -> Result<()> {
        let v = if on { "on" } else { "off" };
        let _ = self.mi_simple(&format!("-gdb-set mi-async {v}"));
        Ok(())
    }

    pub fn environment_cd(&mut self, cwd: &str) -> Result<()> {
        self.mi_simple(&format!("-environment-cd {}", shell_escape(cwd)))?;
        Ok(())
    }

    pub fn environment_set(&mut self, name: &str, value: &str) -> Result<()> {
        self.mi_simple(&format!(
            "-gdb-set environment {}={}",
            name,
            escape_env_value(value)
        ))?;
        Ok(())
    }

    pub fn break_insert(&mut self, file: &str, line: u32) -> Result<Option<String>> {
        let loc = format!("{}:{}", file, line);
        let pl = self
            .mi_simple(&format!("-break-insert -f {}", shell_escape(&loc)))
            .or_else(|_| self.mi_simple(&format!("-break-insert {}", shell_escape(&loc))))?;
        if let Some(n) = extract_bkpt_number(&pl) {
            Ok(Some(n))
        } else {
            Ok(None)
        }
    }

    /// Insert `file:line`, read GDB-resolved line and `addr`. Leaves the breakpoint installed; caller must delete.
    pub fn break_insert_probe_leave(
        &mut self,
        file: &str,
        line: u32,
    ) -> Result<Option<(String, u32, Option<String>)>> {
        let loc = format!("{}:{}", file, line);
        let pl = match self
            .mi_simple(&format!("-break-insert -f {}", shell_escape(&loc)))
            .or_else(|_| self.mi_simple(&format!("-break-insert {}", shell_escape(&loc))))
        {
            Ok(p) => p,
            Err(_) => return Ok(None),
        };
        let Some(num) = extract_bkpt_number(&pl) else {
            return Ok(None);
        };
        let (bound_line, addr) = mi_break_insert_line_addr(&pl);
        let bound = bound_line.unwrap_or(line);
        let addr = addr.map(String::from);
        Ok(Some((num, bound, addr)))
    }

    /// One CLI `delete` for many breakpoint numbers (faster than N × `-break-delete`).
    pub fn break_delete_console_nums(&mut self, nums: &[String]) -> Result<()> {
        if nums.is_empty() {
            return Ok(());
        }
        let list = nums.join(" ");
        let cmd = format!("delete {list}");
        let _ = self.mi_simple(&format!(
            "-interpreter-exec console {}",
            mi_double_quote(&cmd)
        ))?;
        Ok(())
    }

    pub fn break_delete(&mut self, num: &str) -> Result<()> {
        let _ = self.mi_simple(&format!("-break-delete {num}"));
        Ok(())
    }

    /// Watchpoint (`-break-watch`). `expr` is a C expression or address (e.g. `*0x...`).
    pub fn break_watch(&mut self, expr: &str, access: WatchAccess) -> Result<Option<String>> {
        let flag = match access {
            WatchAccess::Write => "",
            WatchAccess::Read => "-r ",
            WatchAccess::ReadWrite => "-a ",
        };
        let pl = self.mi_simple(&format!("-break-watch {flag}{}", shell_escape(expr)))?;
        Ok(extract_bkpt_number(&pl))
    }

    /// Stop when the inferior receives the given signal (`-catch-signal`). Requires GDB (not all lldb-mi builds).
    pub fn catch_signal(&mut self, sig: &str) -> Result<Option<String>> {
        let pl = self.mi_simple(&format!("-catch-signal {}", shell_escape(sig)))?;
        Ok(extract_bkpt_number(&pl))
    }

    /// Stop on any signal delivery (`-catch-signal all`).
    pub fn catch_signal_all(&mut self) -> Result<Option<String>> {
        let pl = self.mi_simple("-catch-signal all")?;
        Ok(extract_bkpt_number(&pl))
    }

    /// C++ exception throw (`-catch-throw` / `__cxa_throw` breakpoint).
    pub fn catch_cpp_throw(&mut self) -> Result<Option<String>> {
        let pl = self
            .mi_simple("-catch-throw")
            .or_else(|_| self.mi_simple("-break-insert -f __cxa_throw"))?;
        Ok(extract_bkpt_number(&pl))
    }

    /// Source files mapped in the inferior (for DAP `loadedSources`).
    pub fn file_list_exec_source_files(&mut self) -> Result<String> {
        self.mi_simple("-file-list-exec-source-files")
    }

    /// Break at instruction address (DAP `instructionReference`). MI: `-break-insert *ADDR`.
    pub fn break_insert_at_address(
        &mut self,
        instruction_reference: &str,
    ) -> Result<Option<String>> {
        let s = instruction_reference.trim();
        if s.is_empty() {
            return Ok(None);
        }
        let pl = self.mi_simple(&format!("-break-insert *{s}"))?;
        Ok(extract_bkpt_number(&pl))
    }

    /// Shared libraries in the inferior (DAP `modules`).
    /// Tries standard MI, then alternate spellings some lldb-mi builds accept.
    pub fn file_list_shared_libraries(&mut self) -> Result<String> {
        self.mi_simple("-file-list-shared-libraries")
            .or_else(|_| self.mi_simple("-file-list-shared-library"))
    }

    pub fn exec_run(&mut self, args: &[String]) -> Result<String> {
        if !args.is_empty() {
            let mut c = String::from("-exec-arguments");
            for a in args {
                c.push(' ');
                c.push_str(&shell_escape(a));
            }
            let _ = self.mi_simple(&c);
        }
        self.mi_exec_until_stop("-exec-run")
    }

    pub fn exec_continue(&mut self) -> Result<String> {
        self.mi_exec_until_stop("-exec-continue")
    }

    pub fn exec_next(&mut self) -> Result<String> {
        self.mi_exec_until_stop("-exec-next")
    }

    pub fn exec_step(&mut self) -> Result<String> {
        self.mi_exec_until_stop("-exec-step")
    }

    pub fn exec_finish(&mut self) -> Result<String> {
        self.mi_exec_until_stop("-exec-finish")
    }

    /// `-exec-interrupt` then wait for `*stopped` (pause / break all).
    pub fn exec_interrupt(&mut self) -> Result<String> {
        let t = self.send_cmd("-exec-interrupt")?;
        loop {
            let line = self.read_line_raw()?;
            if line.trim().is_empty() {
                continue;
            }
            let tl = line.trim_end();
            match classify_mi_line(tl) {
                Some(MiRecord::Result {
                    token: tok,
                    class: MiResultClass::Error,
                    payload: pl,
                }) if tok == t => {
                    let msg = mi_get_str(pl, "msg").unwrap_or("GDB/MI error");
                    return Err(anyhow!(
                        "{}",
                        debugger_diagnostic_text(
                            DiagnosticId::CliDebuggerGdbMiReported,
                            vec![msg.to_string()],
                        )
                    ));
                }
                Some(MiRecord::Result {
                    token: tok,
                    class: MiResultClass::Done,
                    ..
                }) if tok == t => {
                    // Continue until asynchronous *stopped.
                }
                Some(MiRecord::ExecAsync {
                    class: "stopped",
                    payload,
                }) => {
                    return Ok(payload.to_string());
                }
                _ => {}
            }
        }
    }

    /// Evaluate an expression in the given thread/frame (watch / debug console).
    pub fn data_evaluate_expression(
        &mut self,
        thread: u64,
        frame: u32,
        expr: &str,
    ) -> Result<String> {
        self.thread_select(thread)?;
        let quoted = mi_double_quote(expr);
        self.mi_simple(&format!(
            "-data-evaluate-expression --thread {thread} --frame {frame} {quoted}"
        ))
    }

    /// Assign to a variable in the current stack frame (DAP `setVariable`).
    pub fn set_variable(&mut self, thread: u64, frame: u32, name: &str, value: &str) -> Result<()> {
        if !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            return Err(anyhow!(
                "{}",
                debugger_diagnostic_text(
                    DiagnosticId::CliDebuggerSetVariableNameNotSimpleCIdentifier,
                    vec![],
                )
            ));
        }
        self.thread_select(thread)?;
        self.mi_simple(&format!("-stack-select-frame {frame}"))?;
        let cmd = format!("set var {name} = {value}");
        let mi = format!("-interpreter-exec console {}", mi_double_quote(&cmd));
        self.mi_simple(&mi)?;
        Ok(())
    }

    /// Disassemble a byte range `[start, end)` (GDB `-data-disassemble`, mode 0 = assembly only).
    pub fn data_disassemble_range(&mut self, start: &str, end: &str) -> Result<String> {
        self.mi_simple(&format!("-data-disassemble -s {start} -e {end} -- 0"))
    }

    pub fn thread_select(&mut self, id: u64) -> Result<()> {
        self.mi_simple(&format!("-thread-select {id}"))?;
        Ok(())
    }

    pub fn stack_list_frames(
        &mut self,
        thread: u64,
        low_frame: u32,
        high_frame: u32,
    ) -> Result<String> {
        self.thread_select(thread)?;
        self.mi_simple(&format!("-stack-list-frames {} {}", low_frame, high_frame))
    }

    /// Locals with `numchild` / types (for DAP variable expansion).
    pub fn stack_list_vars_all(&mut self, thread: u64, frame: u32) -> Result<String> {
        self.thread_select(thread)?;
        self.mi_simple(&format!(
            "-stack-list-variables --all-values --frame {frame}"
        ))
    }

    pub fn var_create(&mut self, thread: u64, frame: u32, expr: &str) -> Result<String> {
        self.thread_select(thread)?;
        self.mi_simple(&format!(
            "-var-create --thread {thread} --frame {frame} - * {}",
            mi_double_quote(expr)
        ))
    }

    pub fn var_list_children(&mut self, varobj: &str) -> Result<String> {
        self.mi_simple(&format!("-var-list-children --all-values {varobj}"))
    }

    pub fn var_assign(&mut self, varobj: &str, value_expr: &str) -> Result<String> {
        self.mi_simple(&format!(
            "-var-assign {} {}",
            varobj,
            mi_double_quote(value_expr)
        ))
    }

    pub fn var_delete(&mut self, varobj: &str) -> Result<()> {
        let _ = self.mi_simple(&format!("-var-delete {varobj}"));
        Ok(())
    }

    pub fn target_attach(&mut self, pid: u32) -> Result<()> {
        self.mi_simple(&format!("-target-attach {pid}"))?;
        Ok(())
    }

    pub fn gdb_exit(&mut self) -> Result<()> {
        let _ = self.mi_simple("-gdb-exit");
        let _ = self.child.wait();
        Ok(())
    }

    pub fn kill(&mut self) -> Result<()> {
        let _ = self.child.kill();
        let _ = self.child.wait();
        Ok(())
    }
}

fn shell_escape(s: &str) -> String {
    if s.is_empty() {
        return "\"\"".into();
    }
    if s.chars()
        .all(|c| c.is_ascii_alphanumeric() || "/._-+:@".contains(c))
    {
        s.to_string()
    } else {
        format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
    }
}

fn escape_env_value(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
}

fn mi_double_quote(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

#[derive(Clone, Copy, Debug)]
pub enum WatchAccess {
    Write,
    Read,
    ReadWrite,
}

fn extract_bkpt_number(pl: &str) -> Option<String> {
    let needle = "number=\"";
    let start = pl.find(needle)? + needle.len();
    let end = pl[start..].find('"')?;
    Some(pl[start..start + end].to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escape_simple_path() {
        assert_eq!(shell_escape("/tmp/a.out"), "/tmp/a.out");
    }
}
