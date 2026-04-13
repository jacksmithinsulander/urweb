//! Child process helpers for integration tests.

use std::process::Command;
use std::process::Output;

/// Run a child process and surface spawn errors with contextual panic text.
pub fn command_output(command: &mut Command, context: &str) -> Output {
    match command.output() {
        Ok(output) => output,
        Err(error) => panic!("{context}: {error}"),
    }
}
