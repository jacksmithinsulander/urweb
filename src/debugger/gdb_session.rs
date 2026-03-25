//! Spawn GDB in MI3 mode and exchange commands.

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::thread;

use anyhow::{anyhow, Context, Result};

use super::mi_parse::{classify_mi_line, mi_get_str, MiRecord, MiResultClass};

pub struct GdbSession {
    child: Child,
    stdin: ChildStdin,
    reader: BufReader<std::process::ChildStdout>,
    next_token: u64,
}

impl GdbSession {
    /// Run GDB (`--interpreter=mi3`) or LLDB via **lldb-mi** (`--interpreter=mi2`).
    /// Launch `MIMode`: `gdb` (default) or `lldb` / `lldb-mi`.
    pub fn spawn(exe: &str, mi_mode: &str) -> Result<Self> {
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
        let mut child = child
            .spawn()
            .with_context(|| format!("failed to spawn debugger '{exe}' ({mi_mode})"))?;
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
        let reader = BufReader::new(stdout);
        Ok(Self {
            child,
            stdin,
            reader,
            next_token: 1,
        })
    }

    fn read_line_raw(&mut self) -> Result<String> {
        let mut line = String::new();
        if self.reader.read_line(&mut line)? == 0 {
            return Err(anyhow!("unexpected EOF from GDB stdout"));
        }
        Ok(line)
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
                    return Err(anyhow!("{msg}"));
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
                    return Err(anyhow!("{msg}"));
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
        let pl = self.mi_simple(&format!(
            "-break-watch {flag}{}",
            shell_escape(expr)
        ))?;
        Ok(extract_bkpt_number(&pl))
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
                    return Err(anyhow!("{msg}"));
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
    pub fn set_variable(
        &mut self,
        thread: u64,
        frame: u32,
        name: &str,
        value: &str,
    ) -> Result<()> {
        if !name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            return Err(anyhow!(
                "setVariable name must be a simple C identifier"
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
        self.mi_simple(&format!(
            "-data-disassemble -s {start} -e {end} -- 0"
        ))
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

    pub fn stack_list_vars(&mut self, thread: u64, frame: u32) -> Result<String> {
        self.stack_list_vars_all(thread, frame)
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
        self.mi_simple(&format!(
            "-var-list-children --all-values {varobj}"
        ))
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
