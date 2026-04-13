//! Bounded [`ur::compiler`] entrypoints for integration tests (timeout + larger stack).

use std::path::PathBuf;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use ur::compiler;
use ur::settings::Settings;

/// Per-invocation wall clock limit so a broken / pathological compiler mutant fails fast
/// instead of running until cargo-mutants' whole-crate test timeout (~108s).
pub const COMPILE_TO_OUTPUTS_TEST_TIMEOUT: Duration = Duration::from_secs(45);

/// Stack size for the compile worker thread (bytes).
const COMPILE_THREAD_STACK_SIZE: usize = 16 * 1024 * 1024;

/// Run [`compiler::compile_to_outputs`] in a joinable context with a hard
/// timeout. Preserves `Ok` / `Err` from the compiler; maps hangs to `Err`.
pub fn compile_to_outputs_bounded(
    urp: PathBuf,
    configure: impl FnOnce(&mut Settings) + Send + 'static,
) -> anyhow::Result<(String, String)> {
    type R = anyhow::Result<(String, String)>;
    let urp_display = urp.display().to_string();
    let (tx, rx) = mpsc::channel::<R>();
    thread::Builder::new()
        .stack_size(COMPILE_THREAD_STACK_SIZE)
        .spawn(move || {
            let mut settings = Settings::new();
            configure(&mut settings);
            let r = compiler::compile_to_outputs(&urp, &mut settings);
            let _ = tx.send(r);
        })
        .map_err(|e| anyhow::anyhow!("failed to spawn compile thread: {e}"))?;
    match rx.recv_timeout(COMPILE_TO_OUTPUTS_TEST_TIMEOUT) {
        Ok(r) => r,
        Err(mpsc::RecvTimeoutError::Timeout) => Err(anyhow::anyhow!(
            "compile_to_outputs exceeded {:?} (hung or pathologically slow) for {urp_display}",
            COMPILE_TO_OUTPUTS_TEST_TIMEOUT,
        )),
        Err(mpsc::RecvTimeoutError::Disconnected) => Err(anyhow::anyhow!(
            "compile_to_outputs panicked or aborted for {urp_display}",
        )),
    }
}
