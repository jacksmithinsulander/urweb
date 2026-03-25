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
    pub fn spawn(gdb_path: &str) -> Result<Self> {
        let mut child = Command::new(gdb_path)
            .arg("-q")
            .arg("--interpreter=mi3")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .with_context(|| format!("failed to spawn GDB '{gdb_path}'"))?;
        let stdin = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        let stderr = child.stderr.take().unwrap();
        thread::spawn(move || {
            let mut br = BufReader::new(stderr);
            let mut line = String::new();
            while br.read_line(&mut line).unwrap_or(0) > 0 {
                eprint!("[ur-debugger gdb] {line}");
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
        self.thread_select(thread)?;
        self.mi_simple(&format!(
            "-stack-list-variables --simple-values --frame {frame}"
        ))
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
