//! ur-install — Install Ur/Web package via git submodule.

use std::process;
use ur::cli_common;

fn install_package(spec: &str) -> i32 {
    let repo_name = cli_common::package_spec_repo_leaf(spec);

    if let Err(e) = cli_common::ensure_ur_toml_present_for_install() {
        eprintln!("{}", e);
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

    let lib_urp = format!("packages/{}/{}", repo_name, repo_name);
    println!("Installed {} at {}", spec, pkg_dir);
    println!("Add to your .urp:  library {}", lib_urp);
    0
}

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
