//! Debug Adapter Protocol stdio framing (Content-Length).
//!
//! LangSec-style bounds: header lines and body size are capped so a hostile peer cannot spin forever
//! on headers or force an OOM-sized allocation via a giant `Content-Length`.

use std::io::{self, BufRead, Read, Write};

/// Maximum CRLF-delimited header lines before the blank line that ends the header block.
pub const DAP_FRAMING_MAX_HEADER_LINES: usize = 64;

/// Maximum JSON body bytes read after `Content-Length` (inclusive hard cap).
pub const DAP_FRAMING_MAX_BODY_BYTES: usize = 64 * 1024 * 1024;

/// Read one JSON-RPC message. Returns `None` on clean EOF before any byte.
pub fn read_dap_message<R: Read + BufRead>(
    reader: &mut R,
) -> io::Result<Option<serde_json::Value>> {
    let mut line = String::new();
    let mut len: Option<usize> = None;
    let mut header_lines_read = 0usize; // Count non-empty header lines to bound header parsing work.
    loop {
        if header_lines_read >= DAP_FRAMING_MAX_HEADER_LINES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "DAP framing: too many header lines before blank line",
            ));
        }
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        let h = line.trim_end_matches(['\r', '\n']);
        if h.is_empty() {
            break;
        }
        header_lines_read += 1;
        if let Some(rest) = h.strip_prefix("Content-Length:") {
            len = Some(rest.trim().parse().map_err(|_| {
                io::Error::new(io::ErrorKind::InvalidData, "invalid Content-Length")
            })?);
        }
    }
    let n =
        len.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing Content-Length"))?;
    if n > DAP_FRAMING_MAX_BODY_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "DAP framing: Content-Length exceeds maximum allowed body size",
        ));
    }
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
    use std::io::Cursor;

    #[test]
    fn framing_roundtrip() {
        let msg = json!({"seq": 1, "type": "event", "event": "test", "body": {}});
        let mut buf = Vec::new();
        write_dap_message(&mut buf, &msg).unwrap();
        let mut cur = Cursor::new(buf);
        let read = read_dap_message(&mut cur).unwrap().unwrap();
        assert_eq!(read, msg);
    }

    /// Hostile peer: never sends blank line after endless `X:` headers.
    #[test]
    fn read_rejects_excessive_header_lines() {
        let mut hdr = String::new();
        for idx in 0..DAP_FRAMING_MAX_HEADER_LINES + 4 {
            hdr.push_str(&format!("X-Custom: {idx}\r\n"));
        }
        let mut cur = Cursor::new(hdr.into_bytes());
        let err = read_dap_message(&mut cur).expect_err("expected header line limit");
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }

    /// Hostile peer: `Content-Length` larger than [`DAP_FRAMING_MAX_BODY_BYTES`].
    #[test]
    fn read_rejects_oversized_content_length() {
        let hdr = format!("Content-Length: {}\r\n\r\n", DAP_FRAMING_MAX_BODY_BYTES + 1);
        let mut cur = Cursor::new(hdr.into_bytes());
        let err = read_dap_message(&mut cur).expect_err("expected body cap");
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }
}
