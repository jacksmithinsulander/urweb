//! Debug Adapter Protocol stdio framing (Content-Length).

use std::io::{self, BufRead, Read, Write};

/// Read one JSON-RPC message. Returns `None` on clean EOF before any byte.
pub fn read_dap_message<R: Read + BufRead>(
    reader: &mut R,
) -> io::Result<Option<serde_json::Value>> {
    let mut line = String::new();
    let mut len: Option<usize> = None;
    loop {
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        let h = line.trim_end_matches(['\r', '\n']);
        if h.is_empty() {
            break;
        }
        if let Some(rest) = h.strip_prefix("Content-Length:") {
            len = Some(rest.trim().parse().map_err(|_| {
                io::Error::new(io::ErrorKind::InvalidData, "invalid Content-Length")
            })?);
        }
    }
    let n =
        len.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing Content-Length"))?;
    let mut body = vec![0u8; n];
    reader.read_exact(&mut body)?;
    serde_json::from_slice(&body)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("invalid JSON: {e}")))
        .map(Some)
}

/// Write a complete message (body must already include `seq` per DAP).
pub fn write_dap_message<W: Write>(w: &mut W, msg: &serde_json::Value) -> io::Result<()> {
    let body = serde_json::to_vec(msg)?;
    let header = format!("Content-Length: {}\r\n\r\n", body.len());
    w.write_all(header.as_bytes())?;
    w.write_all(&body)?;
    w.flush()?;
    Ok(())
}

/// Allocate the next outgoing sequence number.
pub fn bump_seq(seq: &mut i64) -> i64 {
    *seq += 1;
    *seq
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn framing_roundtrip() {
        let msg = json!({"seq": 1, "type": "event", "event": "test", "body": {}});
        let mut buf = Vec::new();
        write_dap_message(&mut buf, &msg).unwrap();
        let mut cur = io::Cursor::new(buf);
        let read = read_dap_message(&mut cur).unwrap().unwrap();
        assert_eq!(read, msg);
    }
}
