//! ur-new — Create new Ur/Web project scaffold.

use std::process;
use ur::cli_common;
use ur::cli_common::ProjectKind;

fn write_file(path: &str, content: &str) -> std::io::Result<()> {
    std::fs::write(path, content)
}

fn new_project(kind: ProjectKind, name: &str) -> i32 {
    if let Err(e) = cli_common::validate_project_name(name) {
        eprintln!("error: {}", e);
        return 1;
    }
    if std::fs::metadata(name).is_ok() {
        eprintln!("error: '{}' already exists", name);
        return 1;
    }

    if let Err(e) = std::fs::create_dir(name) {
        eprintln!("error: {}", e);
        return 1;
    }

    let mod_name = cli_common::capitalize(name);

    let result: std::io::Result<()> = (|| {
        match kind {
            ProjectKind::App => {
                write_file(
                    &format!("{}/{}.urp", name, name),
                    &format!(
                        "file /style/css/main.css style/css/main.css text/css\n\n{}\n",
                        name
                    ),
                )?;
                write_file(
                    &format!("{}/{}.ur", name, name),
                    &format!(
                        "fun main () : transaction page =\n\
                    count <- source 0;\n\
                    return <xml>\n\
                    <head>\n\
                    <title>{mod}</title>\n\
                    <link rel=\"stylesheet\" href=\"/style/css/main.css\"/>\n\
                    </head>\n\
                    <body>\n\
                    <h1>Counter</h1>\n\
                    <dyn signal={{n <- signal count;\n\
                    return <xml><p>Count: {{[n]}}</p></xml>}}/>\n\
                    <button onclick={{fn _ => n <- get count; set count (n + 1)}}>+</button>\n\
                    <button onclick={{fn _ => n <- get count; set count (n - 1)}}>-</button>\n\
                    <button onclick={{fn _ => set count 0}}>Reset</button>\n\
                    </body>\n\
                    </xml>\n",
                        mod = mod_name
                    ),
                )?;
                std::fs::create_dir(format!("{}/style", name))?;
                std::fs::create_dir(format!("{}/style/scss", name))?;
                std::fs::create_dir(format!("{}/style/css", name))?;
                write_file(
                    &format!("{}/style/scss/main.scss", name),
                    "$primary: #3498db;\n\
$bg:      #f5f5f5;\n\
$text:    #333;\n\
\n\
body {\n\
  font-family: sans-serif;\n\
  background: $bg;\n\
  color: $text;\n\
  margin: 0;\n\
  padding: 2rem;\n\
}\n\
\n\
h1 {\n\
  color: $primary;\n\
  margin-bottom: 1rem;\n\
}\n\
\n\
button {\n\
  background: $primary;\n\
  color: white;\n\
  border: none;\n\
  padding: 0.5rem 1rem;\n\
  margin: 0.25rem;\n\
  cursor: pointer;\n\
  border-radius: 4px;\n\
  font-size: 1rem;\n\
\n\
  &:hover {\n\
    opacity: 0.85;\n\
  }\n\
}\n\
\n\
p {\n\
  font-size: 1.5rem;\n\
}\n",
                )?;
                write_file(
                    &format!("{}/style/css/main.css", name),
                    "body {\n\
  font-family: sans-serif;\n\
  background: #f5f5f5;\n\
  color: #333;\n\
  margin: 0;\n\
  padding: 2rem;\n\
}\n\
\n\
h1 {\n\
  color: #3498db;\n\
  margin-bottom: 1rem;\n\
}\n\
\n\
button {\n\
  background: #3498db;\n\
  color: white;\n\
  border: none;\n\
  padding: 0.5rem 1rem;\n\
  margin: 0.25rem;\n\
  cursor: pointer;\n\
  border-radius: 4px;\n\
  font-size: 1rem;\n\
}\n\
\n\
button:hover {\n\
  opacity: 0.85;\n\
}\n\
\n\
p {\n\
  font-size: 1.5rem;\n\
}\n",
                )?;
                write_file(
                    &format!("{}/ur.toml", name),
                    &format!(
                        "[package]\nname = \"{n}\"\nkind = \"app\"\n\n\
[build]\nentry     = \"{n}\"\ndb        = \"sqlite\"\nccompiler = \"gcc\"\nboot      = false\n\n\
[style]\nscss = \"style/scss/main.scss\"\ncss  = \"style/css/main.css\"\n",
                        n = name
                    ),
                )?;
            }
            ProjectKind::Library => {
                write_file(&format!("{}/{}.urp", name, name), &format!("{}\n", name))?;
                write_file(
                    &format!("{}/{}.urs", name, name),
                    "val add : int -> int -> int\n\
val greet : string -> string\n",
                )?;
                write_file(
                    &format!("{}/{}.ur", name, name),
                    "fun add (x : int) (y : int) : int = x + y\n\
\n\
fun greet (name : string) : string = \"Hello, \" ^ name ^ \"!\"\n",
                )?;
                write_file(
                    &format!("{}/ur.toml", name),
                    &format!(
                        "[package]\nname = \"{n}\"\nkind = \"lib\"\n\n\
[build]\nentry = \"{n}\"\nboot  = false\n",
                        n = name
                    ),
                )?;
            }
        }

        write_file(&format!("{}/cursor.md", name), cli_common::CURSOR_MD)?;
        write_file(&format!("{}/claude.md", name), cli_common::CLAUDE_MD)?;

        let gitignore = match kind {
            ProjectKind::App => format!(
                "{}{}",
                cli_common::GITIGNORE,
                cli_common::GITIGNORE_APP_SUFFIX
            ),
            ProjectKind::Library => cli_common::GITIGNORE.to_string(),
        };
        write_file(&format!("{}/.gitignore", name), &gitignore)?;
        Ok(())
    })();

    if let Err(e) = result {
        eprintln!("error: {}", e);
        return 1;
    }

    // Attempt git init (failure is non-fatal)
    let git_ok = std::process::Command::new("git")
        .args(["-C", name, "init", "-q"])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map_or(false, |s| s.success());

    let kind_str = match kind {
        ProjectKind::App => "app",
        ProjectKind::Library => "library",
    };

    let kind_specific = cli_common::kind_specific_created_files(kind, name);
    println!("Created {} '{}'", kind_str, name);
    println!();
    println!("  {name}/{name}.urp");
    println!("  {name}/{name}.ur");
    for line in kind_specific {
        println!("  {line}");
    }
    println!("  {name}/ur.toml");
    println!("  {name}/cursor.md");
    println!("  {name}/claude.md");
    println!("  {name}/.gitignore");
    println!();
    if git_ok {
        println!("  (initialized git repository)");
        println!();
    }
    println!("Build:  cd {name} && ur build");

    0
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let rest = &args[1..];
    let (kind, name) = if rest.first().map_or(false, |s| s == "--lib" || s == "-lib") {
        let n = rest.get(1).map(|s| s.as_str()).unwrap_or("");
        (ProjectKind::Library, n)
    } else {
        let n = rest.first().map(|s| s.as_str()).unwrap_or("");
        (ProjectKind::App, n)
    };
    if name.is_empty() {
        let usage = if kind == ProjectKind::Library {
            "usage: ur-new --lib <name>"
        } else {
            "usage: ur-new <name>"
        };
        eprintln!("{usage}");
        process::exit(1);
    }
    let code = new_project(kind, name);
    process::exit(code);
}
