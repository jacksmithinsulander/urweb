//! Add third-party Ur/Web packages with Git submodules (`ur-install`).
//!
//! Package specs are uniform resource locators or `author/repo` shorthand (implicit `https://github.com/`).

use std::process;
use ur::cli_common;

/// Clone `spec` as a shallow Git submodule under `packages/<repo-leaf>` and print `.urp` hints.
///
/// `spec` is `author/repo` (implicit `https://github.com/`) or a full `git@` / `https:` URL.
/// Returns `0` on success or if already present, `1` when `ur.toml` is missing or Git fails.
/// Prints a suggested `library` line for the project `.urp` file.
fn install_package(spec: &str) -> i32 {
    // Last path segment of `author/repo` for the local directory name.
    let repo_name = cli_common::package_spec_repo_leaf(spec);

    // Requires an existing `ur.toml` so dependency tracking stays project-relative.
    if let Err(e) = cli_common::ensure_ur_toml_present_for_install() {
        eprintln!("{}", e);
        return 1;
    }

    // Ensure parent directory exists for submodule checkout.
    let _ = std::fs::create_dir("packages");

    // Allow full `git@` / `https:` URLs; otherwise assume github.com.
    let github_spec = if spec.contains(':') {
        spec.to_string()
    } else {
        format!("https://github.com/{}", spec)
    };

    let pkg_dir = format!("packages/{}", repo_name);
    if cli_common::file_exists(&pkg_dir) {
        println!("Package '{}' already installed at {}", repo_name, pkg_dir);
        return 0;
    }

    println!("Installing {} ...", spec);
    let status = std::process::Command::new("git")
        .args(["submodule", "add", "--depth=1", &github_spec, &pkg_dir])
        .status();

    if !cli_common::command_succeeded(&status) {
        eprintln!("error: git submodule add failed");
        return 1;
    }

    // Suggest a `library` line pointing at the package’s `.urp` layout convention.
    let lib_urp = format!("packages/{}/{}", repo_name, repo_name);
    println!("Installed {} at {}", spec, pkg_dir);
    println!("Add to your .urp:  library {}", lib_urp);
    0
}

/// Require one package argument, then call [`install_package`].
///
/// Exits with `1` when the spec is missing.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let spec = args.get(1).map(|s| s.as_str()).unwrap_or("");
    if spec.is_empty() {
        eprintln!("usage: ur-install <author/repo>");
        process::exit(1);
    }
    let code = install_package(spec);
    process::exit(code);
}
