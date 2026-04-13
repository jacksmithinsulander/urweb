//! Debug Adapter Protocol stdio framing (Content-Length).
//!
//! LangSec-style bounds: header lines and body size are capped so a hostile peer cannot spin forever
//! on headers or force an OOM-sized allocation via a giant `Content-Length`.
//!
//! Power-of-ten style: small message bodies use a **fixed stack array** ([`DAP_FRAMING_STACK_BODY_MAX`]);
//! larger bodies use one heap `Vec` bounded by [`DAP_FRAMING_MAX_BODY_BYTES`]. Header lines are
//! length-capped ([`DAP_FRAMING_MAX_HEADER_LINE_BYTES`]) so `read_line` cannot grow without bound.

use std::io::{self, BufRead, Read, Write};

/// Maximum CRLF-delimited header lines before the blank line that ends the header block.
pub const DAP_FRAMING_MAX_HEADER_LINES: usize = 64;

/// Maximum JSON body bytes read after `Content-Length` (inclusive hard cap).
pub const DAP_FRAMING_MAX_BODY_BYTES: usize = 64 * 1024 * 1024;

/// Maximum bytes for one CRLF-terminated header line (excluding line terminator).
///
/// Keeps [`BufRead::read_line`] buffers from growing without bound on a hostile peer.
pub const DAP_FRAMING_MAX_HEADER_LINE_BYTES: usize = 4096;

/// Bodies this size or smaller use a fixed stack buffer (no heap body allocation).
///
/// Must not exceed [`DAP_FRAMING_MAX_BODY_BYTES`]. Typical DAP requests are small JSON.
pub const DAP_FRAMING_STACK_BODY_MAX: usize = 8192;

/// Read one JSON-RPC message. Returns `None` on clean EOF before any byte.
pub fn read_dap_message<R: Read + BufRead>(
    reader: &mut R,
) -> io::Result<Option<serde_json::Value>> {
    let mut line = String::new();
    let mut len: Option<usize> = None;
    let header_scan_budget = DAP_FRAMING_MAX_HEADER_LINES.saturating_add(2);
    let mut saw_header_blank_line = false;
    let mut non_blank_header_markers: Vec<()> = Vec::new();
    for _header_scan_round in 0..header_scan_budget {
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        if line.len() > DAP_FRAMING_MAX_HEADER_LINE_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "DAP framing: header line exceeds maximum length",
            ));
        }
        let h = line.trim_end_matches(['\r', '\n']);
        if h.is_empty() {
            saw_header_blank_line = true;
            break;
        }
        if non_blank_header_markers.len() >= DAP_FRAMING_MAX_HEADER_LINES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "DAP framing: too many header lines before blank line",
            ));
        }
        non_blank_header_markers.push(());
        if let Some(rest) = h.strip_prefix("Content-Length:") {
            len = Some(rest.trim().parse().map_err(|_| {
                io::Error::new(io::ErrorKind::InvalidData, "invalid Content-Length")
            })?);
        }
    }
    if !saw_header_blank_line {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "DAP framing: header scan budget exhausted before blank line",
        ));
    }
    let n =
        len.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing Content-Length"))?;
    if n > DAP_FRAMING_MAX_BODY_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "DAP framing: Content-Length exceeds maximum allowed body size",
        ));
    }
    if n <= DAP_FRAMING_STACK_BODY_MAX {
        let mut stack_body = [0u8; DAP_FRAMING_STACK_BODY_MAX];
        reader.read_exact(&mut stack_body[..n])?;
        return serde_json::from_slice(&stack_body[..n])
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("invalid JSON: {e}")))
            .map(Some);
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
    fn framing_roundtrip() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let msg = json!({"seq": 1, "type": "event", "event": "test", "body": {}});
        let mut buf = Vec::new();
        write_dap_message(&mut buf, &msg)?;
        let mut cur = Cursor::new(buf);
        // unwrap the Option to get Value; None means unexpected EOF
        let read = read_dap_message(&mut cur)?
            .ok_or_else(|| anyhow::anyhow!("expected message but got EOF"))?;
        assert_eq!(read, msg);
        Ok(()) // return success to the test harness
    }

    /// Hostile peer: never sends blank line after endless `X:` headers.
    #[test]
    fn read_rejects_excessive_header_lines() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut hdr = String::new();
        for idx in 0..DAP_FRAMING_MAX_HEADER_LINES + 4 {
            hdr.push_str(&format!("X-Custom: {idx}\r\n"));
        }
        let mut cur = Cursor::new(hdr.into_bytes());
        let err = read_dap_message(&mut cur).expect_err("expected header line limit");
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        Ok(()) // return success to the test harness
    }

    /// Hostile peer: `Content-Length` larger than [`DAP_FRAMING_MAX_BODY_BYTES`].
    #[test]
    fn read_rejects_oversized_content_length() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let hdr = format!("Content-Length: {}\r\n\r\n", DAP_FRAMING_MAX_BODY_BYTES + 1);
        let mut cur = Cursor::new(hdr.into_bytes());
        let err = read_dap_message(&mut cur).expect_err("expected body cap");
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        Ok(()) // return success to the test harness
    }

    /// Hostile peer: one header line longer than [`DAP_FRAMING_MAX_HEADER_LINE_BYTES`].
    #[test]
    fn read_rejects_overlong_header_line() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut hdr = String::with_capacity(DAP_FRAMING_MAX_HEADER_LINE_BYTES + 32);
        hdr.push_str("X-Long: ");
        hdr.push_str(&"y".repeat(DAP_FRAMING_MAX_HEADER_LINE_BYTES + 2));
        hdr.push_str("\r\n\r\n");
        let mut cur = Cursor::new(hdr.into_bytes());
        let err = read_dap_message(&mut cur).expect_err("expected header line cap");
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        Ok(()) // return success to the test harness
    }

    /// Bodies with `Content-Length` exactly [`DAP_FRAMING_STACK_BODY_MAX`] use the stack buffer path.
    #[test]
    fn read_stack_body_exact_max_roundtrip() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Find padding length so `{"a":"<xs>"}` serializes to exactly [`DAP_FRAMING_STACK_BODY_MAX`] bytes.
        let mut pad_len = DAP_FRAMING_STACK_BODY_MAX.saturating_sub(16);
        let mut body = String::new();
        for _ in 0..64 {
            body = format!(r#"{{"a":"{}"}}"#, "x".repeat(pad_len));
            match body.len().cmp(&DAP_FRAMING_STACK_BODY_MAX) {
                std::cmp::Ordering::Equal => break,
                std::cmp::Ordering::Less => pad_len += 1,
                std::cmp::Ordering::Greater => pad_len -= 1,
            }
        }
        assert_eq!(body.len(), DAP_FRAMING_STACK_BODY_MAX);
        let hdr = format!("Content-Length: {}\r\n\r\n{}", body.len(), body);
        let mut cur = Cursor::new(hdr.into_bytes());
        // unwrap the Option; None means unexpected EOF when a message was expected
        let v = read_dap_message(&mut cur)?
            .ok_or_else(|| anyhow::anyhow!("expected message but got EOF"))?;
        assert_eq!(v["a"], serde_json::json!("x".repeat(pad_len)));
        Ok(()) // return success to the test harness
    }
}
