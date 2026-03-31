//! Add third-party Ur/Web packages with Git submodules (`ur-install`).
//!
//! Package specs are uniform resource locators or `author/repo` shorthand (implicit `https://github.com/`).

use std::process;

use ur::cli_common::{self, cli_diagnostic_text, diagnostic_locale_for_cli, writeln_stdout_line};
use ur::diagnostics::DiagnosticId;

/// Clone `spec` as a shallow Git submodule under `packages/<repo-leaf>` and print `.urp` hints.
///
/// `spec` is `author/repo` (implicit `https://github.com/`) or a full `git@` / `https:` URL.
/// Returns `0` on success or if already present, `1` when `ur.toml` is missing or Git fails.
/// Prints a suggested `library` line for the project `.urp` file.
fn install_package(spec: &str) -> i32 {
    let repo_name = cli_common::package_spec_repo_leaf(spec);
    let locale = diagnostic_locale_for_cli(None);

    if let Err(manifest_error) = cli_common::ensure_ur_toml_present_for_install() {
        ur::cli_common::writeln_stderr_display(manifest_error);
        return 1;
    }

    let _ = std::fs::create_dir("packages");

    let github_spec = if spec.contains(':') {
        spec.to_string()
    } else {
        format!("https://github.com/{}", spec)
    };

    let pkg_dir = format!("packages/{}", repo_name);
    if cli_common::file_exists(&pkg_dir) {
        let msg = cli_diagnostic_text(
            DiagnosticId::CliInstallPackagePresent,
            vec![repo_name.to_string(), pkg_dir],
            locale,
        );
        writeln_stdout_line(&msg);
        return 0;
    }

    let progress = cli_diagnostic_text(
        DiagnosticId::CliInstallInProgress,
        vec![spec.to_string()],
        locale,
    );
    writeln_stdout_line(&progress);
    let status = std::process::Command::new("git")
        .args(["submodule", "add", "--depth=1", &github_spec, &pkg_dir])
        .status();

    if !cli_common::command_succeeded(&status) {
        let err = cli_diagnostic_text(DiagnosticId::CliInstallGitFailed, vec![], locale);
        ur::cli_common::writeln_stderr_display(err);
        return 1;
    }

    let lib_urp = format!("packages/{}/{}", repo_name, repo_name);
    let done = cli_diagnostic_text(
        DiagnosticId::CliInstallSucceeded,
        vec![spec.to_string(), pkg_dir],
        locale,
    );
    writeln_stdout_line(&done);
    let hint = cli_diagnostic_text(DiagnosticId::CliInstallUrpHint, vec![lib_urp], locale);
    writeln_stdout_line(&hint);
    0
}

/// Require one package argument, then call [`install_package`].
///
/// Exits with `1` when the spec is missing.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let spec = args.get(1).map(|token| token.as_str()).unwrap_or("");
    if spec.is_empty() {
        let locale = diagnostic_locale_for_cli(None);
        let usage = cli_diagnostic_text(DiagnosticId::CliInstallUsage, vec![], locale);
        ur::cli_common::writeln_stderr_display(usage);
        process::exit(1);
    }
    let code = install_package(spec);
    process::exit(code);
}
