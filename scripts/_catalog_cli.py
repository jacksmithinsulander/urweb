# Executed by gen_diagnostic_catalog.py — CLI, orchestrator, and tooling copy (localized).


def _t(en: str, sv: str | None = None, es: str | None = None) -> tuple[str, str, str]:
    """Triple of localized strings; missing sv/es fall back to English."""
    return (en, sv or en, es or en)


_CLI: list[tuple[str, tuple[str, str, str]]] = [
    (
        "CliManifestMissingOrchestrator",
        _t(
            "I couldn't find `ur.toml` in this folder.\n\n"
            "That small file tells Ur/Web what to build. If you don't have a project yet, run:\n\n"
            "  ur new <project-name>\n\n"
            "Then `cd` into the new folder and run this command again.",
            "Jag hittar inte `ur.toml` i den här mappen.\n\n"
            "Den lilla filen säger Ur/Web vad som ska byggas. Om du inte har projekt än, kör:\n\n"
            "  ur new <projektnamn>\n\n"
            "Sedan `cd` in i mappen och försök igen.",
            "No encuentro `ur.toml` en esta carpeta.\n\n"
            "Ese archivo le dice a Ur/Web qué compilar. Si aún no tienes un proyecto:\n\n"
            "  ur new <nombre>\n\n"
            "Luego entra con `cd` y vuelve a ejecutar el comando.",
        ),
    ),
    (
        "CliManifestMissingFmt",
        _t(
            "I need `ur.toml` in the current directory (or list the files you want to format).\n\n"
            "`ur fmt` looks at `ur.toml` to find your modules when you don't pass paths.\n\n"
            "`cd` into your project root, or pass explicit `.ur` / `.urs` files.",
            "Jag behöver `ur.toml` i aktuell katalog (eller skicka in filerna du vill formatera).\n\n"
            "`ur fmt` läser `ur.toml` för att hitta moduler om du inte anger sökvägar.\n\n"
            "`cd` till projektroten, eller ange `.ur` / `.urs` explicit.",
            "Necesito `ur.toml` en el directorio actual (o indica los archivos a formatear).\n\n"
            "`ur fmt` usa `ur.toml` para localizar módulos si no pasas rutas.\n\n"
            "Entra en la raíz del proyecto con `cd`, o pasa los `.ur` / `.urs` explícitos.",
        ),
    ),
    (
        "CliManifestEntryRequired",
        _t(
            "Your `ur.toml` is missing a non-empty `[build] entry = \"…\"` line.\n\n"
            "`entry` should match the main module name (the `Something` in `Something.ur`).",
            "Din `ur.toml` saknar en icke-tom `[build] entry = \"…\"`.\n\n"
            "`entry` ska matcha huvudmodulens namn (`Något` i `Något.ur`).",
            "Tu `ur.toml` no tiene `[build] entry = \"…\"` con un valor no vacío.\n\n"
            "`entry` debe coincidir con el módulo principal (`Algo` en `Algo.ur`).",
        ),
    ),
    (
        "CliUrTomlReadFailed",
        _t(
            "I could not read `ur.toml` from disk.\n\nDetails: {0}",
            "Jag kunde inte läsa `ur.toml` från disk.\n\nDetalj: {0}",
            "No pude leer `ur.toml` del disco.\n\nDetalle: {0}",
        ),
    ),
    (
        "CliUrTomlParseFailed",
        _t(
            "`ur.toml` looks like Tom's Obvious, Minimal Language, but something is off.\n\nDetail: {0}\n\n"
            "Check brackets, quotes, and that you only use keys Ur/Web knows (no stray keys in `[package]` / `[build]` / `[style]`).",
            "`ur.toml` ser ut som TOML men något stämmer inte.\n\nDetalj: {0}\n\n"
            "Kontrollera hakparenteser, citattecken och att du bara använder kända nycklar.",
            "`ur.toml` parece TOML pero algo no encaja.\n\nDetalle: {0}\n\n"
            "Revisa corchetes, comillas y que solo uses claves permitidas.",
        ),
    ),
    (
        "CliUrTomlMissingInstall",
        _t(
            "`ur install` needs to run inside a project folder that already has `ur.toml`.\n\n"
            "`cd` to your project's root (next to `ur.toml`) and try again.",
            "`ur install` måste köras i en projektmapp som redan har `ur.toml`.\n\n"
            "`cd` till projektroten och försök igen.",
            "`ur install` debe ejecutarse en la raíz del proyecto donde está `ur.toml`.\n\n"
            "Haz `cd` allí y repite.",
        ),
    ),
    (
        "CliManifestDatabaseEngineInvalid",
        _t(
            "The database engine in `[build] db = …` is not one Ur/Web understands.\n\n{0}\n\n"
            "Pick a supported engine (for example `sqlite`) or check spelling.",
            "Databasmotorn i `[build] db = …` känns inte igen av Ur/Web.\n\n{0}\n\n"
            "Välj ett stött motor (t.ex. `sqlite`) eller kolla stavning.",
            "El motor en `[build] db = …` no es uno que Ur/Web entienda.\n\n{0}\n\n"
            "Elige uno soportado (por ejemplo `sqlite`) o corrige la ortografía.",
        ),
    ),
    (
        "CliPeerBinaryNotFound",
        _t(
            "I tried to run `{0}`, but your shell cannot find that program on `PATH`.\n\n"
            "After `cargo build`, add the binary folder to `PATH`, for example:\n\n"
            "  export PATH=\"$PWD/target/debug:$PATH\"\n\n"
            "Or install once with `cargo install --path .` so the `ur-*` tools are available everywhere.",
            "Jag försökte köra `{0}`, men skalet hittar inte programmet på `PATH`.\n\n"
            "Efter `cargo build`, lägg till bin-mappen i `PATH`, t.ex.:\n\n"
            "  export PATH=\"$PWD/target/debug:$PATH\"\n\n"
            "Eller `cargo install --path .` så `ur-*` finns överallt.",
            "Intenté ejecutar `{0}`, pero no está en tu `PATH`.\n\n"
            "Tras `cargo build`, añade la carpeta de binarios, por ejemplo:\n\n"
            "  export PATH=\"$PWD/target/debug:$PATH\"\n\n"
            "O instala con `cargo install --path .`.",
        ),
    ),
    (
        "CliScssCompilationFailed",
        _t(
            "Compiling your SCSS stylesheet failed — the CSS file was not updated.\n\n"
            "Check that `sass` or `sassc` works on the command line and that paths in `ur.toml` `[style]` are correct.",
            "Kompilering av SCSS misslyckades — CSS-filen uppdaterades inte.\n\n"
            "Kontrollera att `sass` / `sassc` fungerar och att sökvägar i `ur.toml` `[style]` stämmer.",
            "Falló la compilación SCSS — no se generó el CSS.\n\n"
            "Verifica `sass` / `sassc` y las rutas en `[style]` de `ur.toml`.",
        ),
    ),
    (
        "CliOrchestratorScssCompiling",
        _t(
            "  Compiling SCSS into CSS…",
            "  Kompilerar SCSS till CSS…",
            "  Compilando SCSS a CSS…",
        ),
    ),
    (
        "CliOrchestratorBuildingApp",
        _t(
            "  Building application `{0}` (compile and link)…",
            "  Bygger applikationen `{0}` (kompilera och länka)…",
            "  Compilando la aplicación `{0}` (compilar y enlazar)…",
        ),
    ),
    (
        "CliOrchestratorTypeCheckingLib",
        _t(
            "  Type-checking library `{0}`…",
            "  Typtestar biblioteket `{0}`…",
            "  Comprobando tipos de la biblioteca `{0}`…",
        ),
    ),
    (
        "CliOrchestratorUsageMoreHelp",
        _t(
            "For all compiler flags, run `ur -help` or `ur-compile --help` (same text).",
            "För alla kompilatorflaggor, kör `ur -help` eller `ur-compile --help`.",
            "Para todas las opciones del compilador: `ur -help` o `ur-compile --help`.",
        ),
    ),
    (
        "CliDispatchMissingSubcommand",
        _t(
            "I need a subcommand after `ur` (for example `ur build`).\n\nRun `ur --help` to see the short list.",
            "Jag behöver ett underkommando efter `ur` (t.ex. `ur build`).\n\nKör `ur --help` för listan.",
            "Falta un subcomando tras `ur` (por ejemplo `ur build`).\n\nEjecuta `ur --help`.",
        ),
    ),
    (
        "CliDispatchRunHelpHint",
        _t(
            "Run `ur --help` for a friendly list of subcommands.",
            "Kör `ur --help` för en översikt av underkommandon.",
            "Ejecuta `ur --help` para ver los subcomandos.",
        ),
    ),
    (
        "CliUsageHeading",
        _t("usage:", "användning:", "uso:"),
    ),
    (
        "CliOrchestratorUsageLines",
        _t(
            "  ur new <project-name>\n"
            "  ur new --lib <project-name>\n"
            "  ur build\n"
            "  ur fmt [options] [files...]\n"
            "  ur install author/repo\n"
            "  ur daemon [stop|start]\n"
            "  ur lsp\n"
            "  ur debugger [ur-debugger-args...]\n"
            "  ur [flag ...] project-name",
            "  ur new <projektnamn>\n"
            "  ur new --lib <projektnamn>\n"
            "  ur build\n"
            "  ur fmt [flaggor...] [filer...]\n"
            "  ur install författare/repo\n"
            "  ur daemon [stop|start]\n"
            "  ur lsp\n"
            "  ur debugger [ur-debugger-args...]\n"
            "  ur [flaggor...] projektnamn",
            "  ur new <nombre-proyecto>\n"
            "  ur new --lib <nombre-proyecto>\n"
            "  ur build\n"
            "  ur fmt [opciones...] [archivos...]\n"
            "  ur install autor/repo\n"
            "  ur daemon [stop|start]\n"
            "  ur lsp\n"
            "  ur debugger [ur-debugger-args...]\n"
            "  ur [flags...] nombre-proyecto",
        ),
    ),
    (
        "CliUrCompileHelpExtra",
        _t(
            "Standard options: -h, --help; -V, --version; -o, --output=FILE\n"
            "Compiler-focused flags:\n"
            "  -h, -help, --help      show this overview\n"
            "  -V, -version           print version and exit\n"
            "  -ccompiler <prog>     C compiler to invoke\n"
            "  -dbms <engine>        database engine [sqlite|mysql|postgres|persy|rocksdb|ndb|tigerbeetle|…]\n"
            "  -db <connstr>         connection string for local development databases\n"
            "  -prefix <prefix>      URL prefix for generated links\n"
            "  -sql <file>           write SQL DDL to <file>\n"
            "  -o, -output <file>    place the executable at <file> (--output=FILE also works)\n"
            "  -tc                   stop after type checking (no native code yet)\n"
            "  -debug                 keep intermediate C files for debugging\n"
            "  -v, -vv, … -vvvvv     verbosity (stderr tracing; up to five v's)\n"
            "  -verbose               same spirit as -vv (legacy name)\n"
            "  -timing                print coarse phase timings on stderr\n"
            "  RUST_LOG                optional tracing filter (overrides default ur=…)\n"
            "  -iflow                 run information-flow analysis\n"
            "  -limit <class> <n>     set a resource limit\n"
            "  -startLspServer        run the Language Server on standard input/output\n"
            "  -moduleOf <file>       print the Ur/Web module name for <file>",
            "Standardalternativ: -h, --help; -V, --version; -o, --output=FILE\n"
            "Kompilatorflaggor:\n"
            "  -h, -help, --help      visa denna översikt\n"
            "  -V, -version           skriv version och avsluta\n"
            "  -ccompiler <prog>     C-kompilator att anropa\n"
            "  -dbms <motor>         databasmotor [sqlite|mysql|postgres|…]\n"
            "  -db <anslutn>         anslutningssträng\n"
            "  -prefix <prefix>      URL-prefix\n"
            "  -sql <fil>            skriv SQL-DDL till fil\n"
            "  -o, -output <fil>     utdata-exekverbar fil\n"
            "  -tc                   stoppa efter typtest\n"
            "  -debug                 spara mellanliggande C-filer\n"
            "  -v, -vv, … -vvvvv     stderr-loggning (upp till fem v)\n"
            "  -verbose               liknande -vv (legacy)\n"
            "  -timing                fas-tider på stderr\n"
            "  RUST_LOG                valfritt filter för loggning\n"
            "  -iflow                 informationsflödesanalys\n"
            "  -limit <klass> <n>     resursgräns\n"
            "  -startLspServer        Language Server på stdio\n"
            "  -moduleOf <fil>        skriv modulnamn för fil",
            "Opciones estándar: -h, --help; -V, --version; -o, --output=FILE\n"
            "Banderas del compilador:\n"
            "  -h, -help, --help      muestra esta ayuda\n"
            "  -V, -version           imprime la versión y sale\n"
            "  -ccompiler <prog>     compilador C\n"
            "  -dbms <motor>         motor de base de datos [sqlite|mysql|postgres|…]\n"
            "  -db <cadena>          cadena de conexión\n"
            "  -prefix <prefijo>     prefijo URL\n"
            "  -sql <archivo>        escribe DDL SQL\n"
            "  -o, -output <archivo> ejecutable de salida\n"
            "  -tc                   parar tras chequeo de tipos\n"
            "  -debug                 conserva C intermedio\n"
            "  -v, -vv, … -vvvvv     trazas en stderr\n"
            "  -verbose               alias histórico (~ -vv)\n"
            "  -timing                tiempos por fase en stderr\n"
            "  RUST_LOG                filtro de tracing opcional\n"
            "  -iflow                 análisis de flujo de información\n"
            "  -limit <clase> <n>     límite de recurso\n"
            "  -startLspServer        servidor LSP en stdio\n"
            "  -moduleOf <archivo>    muestra el nombre de módulo",
        ),
    ),
    (
        "CliUrFmtHelp",
        _t(
            "ur-fmt — tidy `.ur` and `.urs` source\n\n"
            "ur-fmt [options] [files...]\n\n"
            "With no files: discovers modules from your `.urp` using `ur.toml` `[build] entry`.\n"
            "With files: formats exactly those paths.\n\n"
            "  --check       exit with status 1 if anything would change\n"
            "  -t, --tab N   tab width when expanding tabs (default 4)\n"
            "  -w, --width N accepted for compatibility (wrapping not implemented yet)",
            "ur-fmt — städa `.ur` och `.urs`\n\n"
            "ur-fmt [flaggor...] [filer...]\n\n"
            "Utan filer: hittar moduler via `.urp` och `ur.toml`.\n"
            "Med filer: formaterar bara dessa.\n\n"
            "  --check       avsluta med 1 om något skulle ändras\n"
            "  -t, --tab N   tabbredd (standard 4)\n"
            "  -w, --width N kompatibilitet (ingen radbrytning än)",
            "ur-fmt — formatea `.ur` y `.urs`\n\n"
            "ur-fmt [opciones...] [archivos...]\n\n"
            "Sin archivos: descubre módulos con `.urp` y `ur.toml`.\n"
            "Con archivos: solo esos.\n\n"
            "  --check       sale con 1 si algo cambiaría\n"
            "  -t, --tab N   ancho de tabulación (4 por defecto)\n"
            "  -w, --width N compatibilidad (sin ajuste de línea aún)",
        ),
    ),
    (
        "CliUrFmtNoSourceFilesFound",
        _t(
            "I scanned your project file but didn't find any `.ur` or `.urs` paths to format.\n\n"
            "Add modules to the `.urp` or pass files on the command line.",
            "Jag läste projektfilen men hittade inga `.ur` eller `.urs` att formatera.\n\n"
            "Lägg till moduler i `.urp` eller ange filer på kommandoraden.",
            "Revisé el proyecto pero no hay rutas `.ur` o `.urs` que formatear.\n\n"
            "Añade módulos al `.urp` o pasa archivos explícitos.",
        ),
    ),
    (
        "CliUrFmtProjectUrpNotFound",
        _t(
            "I expected a project file at `{0}` (next to `ur.toml`) but it is not there.\n\n"
            "Check `[build] entry` — it should match your main module name.",
            "Jag förväntade mig en projektfil på `{0}` men den saknas.\n\n"
            "Kolla `[build] entry` mot huvudmodulens namn.",
            "Esperaba el proyecto en `{0}` pero no existe.\n\n"
            "Revisa `[build] entry` en `ur.toml`.",
        ),
    ),
    (
        "CliUrFmtUnknownFlag",
        _t(
            "I don't know the formatter flag `{0}` — I'll ignore it.\n\nRun `ur fmt --help` for supported options.",
            "Jag känner inte igen formateringsflaggan `{0}` — den ignoreras.\n\nKör `ur fmt --help`.",
            "No reconozco el flag `{0}` del formateador — lo ignoro.\n\nUsa `ur fmt --help`.",
        ),
    ),
    (
        "CliUrFmtNotUrFile",
        _t(
            "`{0}` is not a `.ur` or `.urs` file — I can only format Ur/Web sources.",
            "`{0}` är inte `.ur` eller `.urs` — bara sådana kan formateras.",
            "`{0}` no es `.ur` ni `.urs` — solo esos archivos.",
        ),
    ),
    (
        "CliUrFmtFileMissing",
        _t(
            "I can't find `{0}` on disk.",
            "Jag hittar inte `{0}` på disk.",
            "No encuentro `{0}`.",
        ),
    ),
    (
        "CliUrFmtReadFailed",
        _t(
            "I could not read `{0}`.",
            "Jag kunde inte läsa `{0}`.",
            "No pude leer `{0}`.",
        ),
    ),
    (
        "CliUrFmtCheckWouldChange",
        _t(
            "`{0}` would change if formatted — `--check` stops here.",
            "`{0}` skulle ändras av formatering — `--check` stoppar här.",
            "`{0}` cambiaría al formatear — `--check` detiene aquí.",
        ),
    ),
    (
        "CliUrFmtWriteFailed",
        _t(
            "Could not write `{0}`: {1}",
            "Kunde inte skriva `{0}`: {1}",
            "No pude escribir `{0}`: {1}",
        ),
    ),
    (
        "CliUrFmtParseFailedHeader",
        _t(
            "I couldn't pretty-print `{0}` because parsing failed:",
            "Jag kan inte pretty-printa `{0}` — tolkning misslyckades:",
            "No pude formatear `{0}` porque el análisis falló:",
        ),
    ),
    (
        "CliInstallPackagePresent",
        _t(
            "Good news — `{0}` is already here at `{1}`.\n\nNothing to download.",
            "Bra — `{0}` finns redan på `{1}`.\n\nInget att ladda ner.",
            "Bien — `{0}` ya está en `{1}`.\n\nNo hay nada que descargar.",
        ),
    ),
    (
        "CliInstallInProgress",
        _t(
            "Fetching `{0}` as a Git submodule (shallow clone)…",
            "Hämtar `{0}` som git-undermodul (grund klon)…",
            "Trayendo `{0}` como submódulo Git (clon superficial)…",
        ),
    ),
    (
        "CliInstallSucceeded",
        _t(
            "Installed `{0}` under `{1}`.\n\nNext step: add a `library` line to your `.urp` (see below).",
            "Installerade `{0}` under `{1}`.\n\nNästa steg: lägg till `library` i `.urp` (nedan).",
            "Instalé `{0}` en `{1}`.\n\nSiguiente: añade `library` en tu `.urp` (abajo).",
        ),
    ),
    (
        "CliInstallUrpHint",
        _t(
            "Suggested `.urp` line:\n\n  library {0}",
            "Föreslagen `.urp`-rad:\n\n  library {0}",
            "Línea sugerida para `.urp`:\n\n  library {0}",
        ),
    ),
    (
        "CliInstallGitFailed",
        _t(
            "`git submodule add` did not finish successfully.\n\n"
            "Check your network, Git credentials, and that the URL is valid.",
            "`git submodule add` misslyckades.\n\n"
            "Kolla nätverk, Git-identitet och att URL:en är giltig.",
            "`git submodule add` no terminó bien.\n\n"
            "Revisa red, credenciales Git y que la URL sea válida.",
        ),
    ),
    (
        "CliInstallUsage",
        _t(
            "Usage: `ur install <author/repo>` or a full `https://…` / `git@…` URL.",
            "Användning: `ur install <författare/repo>` eller full `https://…` / `git@…` URL.",
            "Uso: `ur install <autor/repo>` o una URL `https://…` / `git@…` completa.",
        ),
    ),
    (
        "CliDaemonStopped",
        _t(
            "Daemon marker removed — there was nothing else to stop (stub implementation).",
            "Daemon-markör borttagen — inget mer att stoppa (stubb).",
            "Marcador del daemon eliminado — no había más que detener (implementación provisional).",
        ),
    ),
    (
        "CliDaemonNotImplemented",
        _t(
            "The development daemon is not implemented yet — this command is a placeholder.",
            "Utvecklingsdaemonen är inte implementerad än — platshållare.",
            "El daemon de desarrollo aún no está implementado — es un marcador de posición.",
        ),
    ),
    (
        "CliDaemonUsage",
        _t(
            "Usage: `ur-daemon start` or `ur-daemon stop`.",
            "Användning: `ur-daemon start` eller `ur-daemon stop`.",
            "Uso: `ur-daemon start` o `ur-daemon stop`.",
        ),
    ),
    (
        "CliUrNewCreated",
        _t(
            "All set — I created a new {0} named `{1}`.\n\nFiles and folders:",
            "Klart — ny {0} som heter `{1}`.\n\nFiler och mappar:",
            "Listo — nueva {0} llamada `{1}`.\n\nArchivos y carpetas:",
        ),
    ),
    (
        "CliUrNewGitNote",
        _t(
            "  (Git repository initialized in the project folder)",
            "  (Git init kördes i projektmappen)",
            "  (Repositorio Git inicializado en la carpeta del proyecto)",
        ),
    ),
    (
        "CliUrNewBuildHint",
        _t(
            "When you're ready:  cd {0}  &&  ur build",
            "När du är redo:  cd {0}  &&  ur build",
            "Cuando quieras compilar:  cd {0}  &&  ur build",
        ),
    ),
    (
        "CliUrNewUsageApp",
        _t(
            "Usage: `ur-new <project-name>` — creates an application scaffold.",
            "Användning: `ur-new <projektnamn>` — skapar en applikationsmall.",
            "Uso: `ur-new <nombre>` — crea una aplicación base.",
        ),
    ),
    (
        "CliUrNewUsageLib",
        _t(
            "Usage: `ur-new --lib <library-name>` — creates a library scaffold.",
            "Användning: `ur-new --lib <namn>` — skapar ett bibliotek.",
            "Uso: `ur-new --lib <nombre>` — crea una biblioteca base.",
        ),
    ),
    (
        "CliDemoRequiresDirectory",
        _t(
            "`-demo` expects a directory argument after the prefix — I didn't see one.",
            "`-demo` behöver en katalog efter prefixet — jag fick ingen.",
            "`-demo` necesita un directorio tras el prefijo — no apareció ninguno.",
        ),
    ),
    (
        "CliNoProjectSeeHelp",
        _t(
            "I need a project file (usually `Something.urp`) on the command line.\n\nTry `ur-compile --help` for examples.",
            "Jag behöver en projektfil (ofta `Något.urp`) på kommandoraden.\n\nSe `ur-compile --help`.",
            "Necesito un proyecto (p. ej. `Algo.urp`) en la línea de comandos.\n\nMira `ur-compile --help`.",
        ),
    ),
    (
        "CliInvalidLimitNumber",
        _t(
            "`{0}` is not a valid integer for `-limit` — I need a number like `10` or `0`.",
            "`{0}` är inte ett giltigt heltal för `-limit`.",
            "`{0}` no es un entero válido para `-limit`.",
        ),
    ),
    (
        "CliUnknownCompilerFlag",
        _t(
            "I don't recognize the flag `{0}`.\n\nRun `-help` to see supported options.",
            "Jag känner inte igen flaggan `{0}`.\n\nKör `-help`.",
            "No reconozco el flag `{0}`.\n\nUsa `-help`.",
        ),
    ),
    (
        "CliCompilerWorkerSpawnFailed",
        _t(
            "I could not start the compiler worker thread (stack size {0} bytes).\n\nReason: {1}\n\n"
            "Try closing heavy programs or raising the stack limit for this shell.",
            "Kunde inte starta kompilatorns worker-tråd (stack {0} byte).\n\nOrsak: {1}",
            "No pude iniciar el hilo compilador (pila {0} bytes).\n\nMotivo: {1}",
        ),
    ),
    (
        "CliCompilerWorkerPanicked",
        _t(
            "The compiler worker thread panicked — that usually means an internal compiler bug.\n\n"
            "If you can reproduce this with a tiny project, please report it with the source.",
            "Worker-tråden panikerade — oftast en kompilatorbugg.\n\n"
            "Om du kan reproducera med ett minimiprojekt, rapportera gärna.",
            "El hilo del compilador entró en pánico — suele ser un fallo interno.\n\n"
            "Si puedes reproducirlo con un proyecto mínimo, repórtalo.",
        ),
    ),
    (
        "CliCompilerPhaseTiming",
        _t(
            "  · {0}: {1} ms",
            "  · {0}: {1} ms",
            "  · {0}: {1} ms",
        ),
    ),
    (
        "CliDumpOutputUsage",
        _t(
            "Usage: dump_output <path-to.urp> <output.c> <output.sql>",
            "Användning: dump_output <väg.urp> <ut.c> <ut.sql>",
            "Uso: dump_output <ruta.urp> <salida.c> <salida.sql>",
        ),
    ),
    (
        "CliDumpOutputChdirFailed",
        _t(
            "I could not `cd` into `{0}`: {1}",
            "Kunde inte `cd` till `{0}`: {1}",
            "No pude hacer `cd` a `{0}`: {1}",
        ),
    ),
    (
        "CliDumpOutputCompileFailed",
        _t(
            "Compilation stopped before I could write C/SQL outputs.\n\n{0}",
            "Kompilering stoppade innan C/SQL kunde skrivas.\n\n{0}",
            "La compilación falló antes de escribir C/SQL.\n\n{0}",
        ),
    ),
    (
        "CliTestParseHasErrors",
        _t(
            "Reporter reports errors: {0}",
            "Rapporten har fel: {0}",
            "El reporte indica errores: {0}",
        ),
    ),
    (
        "CliTestParseDeclCount",
        _t(
            "Parsed declaration count: {0}",
            "Antal tolkade deklarationer: {0}",
            "Cantidad de declaraciones analizadas: {0}",
        ),
    ),
    (
        "CliTestParseFailed",
        _t(
            "Parse failed (no declaration count).",
            "Tolkning misslyckades (inget antal).",
            "El análisis falló.",
        ),
    ),
    (
        "CliTestParseTwoDecls",
        _t(
            "Second sample — declaration count: {0}",
            "Andra exemplet — antal deklarationer: {0}",
            "Segunda muestra — declaraciones: {0}",
        ),
    ),
    (
        "CliTestParseTwoDeclsFailed",
        _t(
            "Second sample — parse failed.",
            "Andra exemplet — tolkning misslyckades.",
            "Segunda muestra — análisis fallido.",
        ),
    ),
    (
        "CliTestPpContextOk",
        _t(
            "Preprocessor window (debug): {0}",
            "Preprocessorfönster (debug): {0}",
            "Ventana del preprocessador (depuración): {0}",
        ),
    ),
    (
        "CliFileReadFailed",
        _t(
            "I could not read `{0}`.\n\nDetail: {1}",
            "Jag kunde inte läsa `{0}`.\n\nDetalj: {1}",
            "No pude leer `{0}`.\n\nDetalle: {1}",
        ),
    ),
    (
        "CliTomlParseAtPathFailed",
        _t(
            "`{0}` should be valid Tom's Obvious, Minimal Language, but parsing failed.\n\nDetail: {1}",
            "`{0}` ska vara giltig TOML men tolkning misslyckades.\n\nDetalj: {1}",
            "`{0}` debería ser TOML válido pero falló el análisis.\n\nDetalle: {1}",
        ),
    ),
    (
        "CliPackageLanguageInvalid",
        _t(
            "`ur.toml` `[package] language` is `{0}`.\n\nPlease use `en`, `sv`, or `es` (or omit the key for English).",
            "`ur.toml` `[package] language` är `{0}`.\n\nAnvänd `en`, `sv` eller `es` (eller utelämna nyckeln).",
            "`ur.toml` `[package] language` es `{0}`.\n\nUsa `en`, `sv` o `es` (u omite la clave).",
        ),
    ),
    (
        "CliBuildDatabaseEngineMismatch",
        _t(
            "`ur.toml` says the database engine is `{0}`, but this build is using `{1}` (from `-dbms`, your `.urp`, or the default).\n\nThose must match — adjust `ur.toml` `[build] db` or your build flags.",
            "`ur.toml` anger databasmotor `{0}`, men bygget använder `{1}`.\n\nJustera så de stämmer överens.",
            "`ur.toml` indica motor `{0}`, pero la compilación usa `{1}`.\n\nDeben coincidir.",
        ),
    ),
    (
        "CliProjectNameEmpty",
        _t(
            "The project name cannot be empty.\n\nPick a short identifier like `myapp` (letters, digits, underscores).",
            "Projektnamnet får inte vara tomt.\n\nVälj t.ex. `myapp` (bokstäver, siffror, understreck).",
            "El nombre del proyecto no puede estar vacío.\n\nUsa algo como `myapp` (letras, dígitos, guiones bajos).",
        ),
    ),
    (
        "CliProjectNameMustStartWithLetter",
        _t(
            "Project name `{0}` must start with a letter.",
            "Projektnamnet `{0}` måste börja med en bokstav.",
            "El nombre `{0}` debe empezar con una letra.",
        ),
    ),
    (
        "CliProjectNameInvalidCharacters",
        _t(
            "Project name `{0}` may only contain letters, digits, and underscores (no hyphens or spaces).",
            "Projektnamnet `{0}` får bara innehålla bokstäver, siffror och understreck.",
            "El nombre `{0}` solo puede tener letras, dígitos y guiones bajos.",
        ),
    ),
    (
        "CliUrNewDirectoryExists",
        _t(
            "A file or folder named `{0}` already exists here.\n\nPick a fresh name or remove it first.",
            "Något som heter `{0}` finns redan här.\n\nVälj ett nytt namn eller ta bort det först.",
            "Ya existe `{0}` aquí.\n\nElige otro nombre o elimínalo primero.",
        ),
    ),
    (
        "CliUrNewScaffoldIoFailed",
        _t(
            "I hit an input/output problem while creating the project files.\n\n{0}",
            "Ett I/O-fel uppstod när projektfilerna skulle skapas.\n\n{0}",
            "Hubo un error de E/S al crear los archivos del proyecto.\n\n{0}",
        ),
    ),
    (
        "CliDatabaseBackendCliRejected",
        _t(
            "I could not configure the database engine from the command line.\n\n{0}",
            "Jag kunde inte ställa in databasmotorn från kommandoraden.\n\n{0}",
            "No pude configurar el motor de base de datos desde la línea de comandos.\n\n{0}",
        ),
    ),
    (
        "CliCompileResourceLimitConfiguration",
        _t(
            "Invalid resource limit configuration.\n\n{0}",
            "Ogiltig resursgräns.\n\n{0}",
            "Configuración de límite de recurso no válida.\n\n{0}",
        ),
    ),
    (
        "CliDemoModeFailed",
        _t(
            "Demo mode stopped before finishing.\n\n{0}",
            "Demonstrationsläge avbröts.\n\n{0}",
            "El modo demo se detuvo antes de terminar.\n\n{0}",
        ),
    ),
    (
        "CliLspRunFailed",
        _t(
            "The Language Server exited with an error.\n\n{0}",
            "Language Server avslutades med fel.\n\n{0}",
            "El servidor de lenguaje terminó con error.\n\n{0}",
        ),
    ),
    (
        "CliLspProjectOpenFailed",
        _t(
            "I could not load the Ur/Web project in this workspace.\n\n{0}",
            "Jag kunde inte ladda Ur/Web-projektet i arbetsytan.\n\n{0}",
            "No pude cargar el proyecto Ur/Web en este espacio de trabajo.\n\n{0}",
        ),
    ),
    (
        "CliLspWorkspaceChdirFailed",
        _t(
            "I could not `cd` into the workspace root `{0}`.\n\nDetail: {1}",
            "Kunde inte `cd` till arbetsytesroten `{0}`.\n\nDetalj: {1}",
            "No pude hacer `cd` a la raíz `{0}`.\n\nDetalle: {1}",
        ),
    ),
    (
        "CliLspWorkspaceReadDirFailed",
        _t(
            "I could not read the workspace directory `{0}`.\n\n{1}",
            "Jag kunde inte läsa arbetsytesmappen `{0}`.\n\n{1}",
            "No pude leer el directorio del espacio de trabajo `{0}`.\n\n{1}",
        ),
    ),
    (
        "CliLspWorkspaceDirEntryFailed",
        _t(
            "I could not read a directory entry while scanning `{0}`.\n\n{1}",
            "Jag kunde inte läsa en katalogpost vid skanning av `{0}`.\n\n{1}",
            "No pude leer una entrada del directorio al examinar `{0}`.\n\n{1}",
        ),
    ),
    (
        "CliLspWorkspaceNoUrProjectFile",
        _t(
            "No `.urp` project file was found in `{0}`. Open a folder that contains exactly one `.urp` file.",
            "Ingen `.urp`-projektfil hittades i `{0}`. Öppna en mapp som innehåller exakt en `.urp`-fil.",
            "No se encontró ningún proyecto `.urp` en `{0}`. Abre una carpeta con exactamente un archivo `.urp`.",
        ),
    ),
    (
        "CliLspWorkspaceUrpPathInternal",
        _t(
            "Internal error: expected one `.urp` path after scanning `{0}`.",
            "Internt fel: förväntade en `.urp`-sökväg efter skanning av `{0}`.",
            "Error interno: se esperaba una ruta `.urp` tras examinar `{0}`.",
        ),
    ),
    (
        "CliLspWorkspaceMultipleUrProjectFiles",
        _t(
            "Multiple `.urp` files were found in `{0}`: {1}. Use a workspace folder with a single project file.",
            "Flera `.urp`-filer hittades i `{0}`: {1}. Använd en arbetsyta med endast en projektfil.",
            "Hay varios archivos `.urp` en `{0}`: {1}. Usa una carpeta de trabajo con un solo proyecto.",
        ),
    ),
    (
        "CliLspProjectResolveFailed",
        _t(
            "I could not load the Ur/Web project file `{0}`.\n\n{1}",
            "Jag kunde inte ladda Ur/Web-projektfilen `{0}`.\n\n{1}",
            "No pude cargar el archivo de proyecto Ur/Web `{0}`.\n\n{1}",
        ),
    ),
    (
        "CliCompileStoppedAfterDiagnostics",
        _t(
            "I stopped after {0} because there were {1} hard error(s) above this line.\n\n"
            "Each one uses the same layout as the Ur/Web compiler. Fix the first error first — later lines are often knock-on effects.",
            "Jag stoppade efter {0} eftersom det fanns {1} hårda fel ovan.\n\n"
            "Åtgärda det första felet först — resten följer ofta av det.",
            "Me detuve tras {0} porque había {1} error(es) grave(s) arriba.\n\n"
            "Corrige primero el primero; el resto suele ser consecuencia.",
        ),
    ),
    (
        "CliCCompilerRejectedGeneratedFile",
        _t(
            "The C compiler (`{0}`, exit {1}) rejected the generated file `{2}`.\n\n"
            "Ur/Web already produced this C from your sources; the problem is now in the C toolchain. "
            "Typical fixes: check `-I` paths to the runtime headers, `-ccompiler`, or run the same command manually to see the exact line.",
            "C-kompilatorn (`{0}`, exit {1}) godkände inte `{2}`.\n\n"
            "Ur/Web har redan genererat C; felet sitter i verktygskedjan. Kontrollera `-I`, `-ccompiler`, eller kör kommandot manuellt.",
            "El compilador C (`{0}`, código {1}) rechazó `{2}`.\n\n"
            "Ur/Web ya generó ese C; el fallo está en la cadena de herramientas. Revisa `-I`, `-ccompiler` o ejecuta el mismo comando a mano.",
        ),
    ),
    (
        "CliLinkerCouldNotProduceExecutable",
        _t(
            "The linker (`{0}`, exit {1}) could not produce `{2}`.\n\n"
            "The object file `{3}` built successfully. Check `liburweb`, database client libraries, `-L` paths, and flags such as BearSSL or `URWEB_NATIVE_LIB_DIR`.",
            "Länkaren (`{0}`, exit {1}) kunde inte skapa `{2}`.\n\n"
            "Objektfilen `{3}` finns. Kontrollera `liburweb`, databasbibliotek och sökvägar.",
            "El enlazador (`{0}`, código {1}) no pudo crear `{2}`.\n\n"
            "El objeto `{3}` sí se compiló. Revisa `liburweb`, bibliotecas de DB y `-L`.",
        ),
    ),
    (
        "CliWriteGeneratedCFileFailed",
        _t(
            "I could not write the generated C source to `{0}`.\n\n{1}",
            "Kunde inte skriva genererad C-källa till `{0}`.\n\n{1}",
            "No pude escribir el C generado en `{0}`.\n\n{1}",
        ),
    ),
    (
        "CliToolBannerCompileStopped",
        _t(
            "COMPILE STOPPED",
            "KOMPILERING STOPPAD",
            "COMPILACIÓN DETENIDA",
        ),
    ),
    (
        "CliToolBannerCBuild",
        _t(
            "C BUILD",
            "C-BYGG",
            "COMPILACIÓN C",
        ),
    ),
    (
        "CliToolBannerLink",
        _t(
            "LINK",
            "LÄNKNING",
            "ENLACE",
        ),
    ),
    (
        "CliCompileWriteSqlFileFailed",
        _t(
            "I could not write generated SQL to `{0}`.\n\n{1}",
            "Kunde inte skriva genererad SQL till `{0}`.\n\n{1}",
            "No pude escribir el SQL generado en `{0}`.\n\n{1}",
        ),
    ),
    (
        "CliUrpDirectiveParseFailed",
        _t(
            "This line in your `.urp` project file could not be processed:\n\n`{0}`\n\n{1}",
            "Denna rad i `.urp`-projektfilen kunde inte hanteras:\n\n`{0}`\n\n{1}",
            "No pude procesar esta línea del proyecto `.urp`:\n\n`{0}`\n\n{1}",
        ),
    ),
    (
        "CliUrpInvalidUnsignedIntegerDirective",
        _t(
            "The `{0}` directive needs a non-negative integer. I could not parse `{1}`.",
            "Direktivet `{0}` kräver ett icke-negativt heltal. Kunde inte tolka `{1}`.",
            "La directiva `{0}` necesita un entero no negativo. No pude interpretar `{1}`.",
        ),
    ),
    (
        "CliSubprocessSpawnFailed",
        _t(
            "Could not start a subprocess for this step: {0}\n\n{1}",
            "Kunde inte starta underprocess för detta steg: {0}\n\n{1}",
            "No pude iniciar un subproceso para este paso: {0}\n\n{1}",
        ),
    ),
    (
        "CliSubprocessPollFailed",
        _t(
            "Could not poll a subprocess for this step: {0}\n\n{1}",
            "Kunde inte avfråga underprocess för detta steg: {0}\n\n{1}",
            "No pude consultar el subproceso para este paso: {0}\n\n{1}",
        ),
    ),
    (
        "CliSubprocessRunFailed",
        _t(
            "Could not run this subprocess step: {0}\n\n{1}",
            "Kunde inte köra detta underprocesssteg: {0}\n\n{1}",
            "No pude ejecutar este paso de subproceso: {0}\n\n{1}",
        ),
    ),
    (
        "CliCompilerCcLinkTestDeadlineExceeded",
        _t(
            "Subprocess step `{0}` exceeded the test-only deadline ({1}).\n\n"
            "If you see this outside mutation tests, report it as a bug.",
            "Underprocess `{0}` överskred testtidsgränsen ({1}).\n\n"
            "Om du ser detta utanför mutationstester, rapportera som bugg.",
            "El subproceso `{0}` superó el límite de prueba ({1}).\n\n"
            "Si no estás en tests de mutación, repórtalo.",
        ),
    ),
    (
        "CliUrpFfiExpectedModuleDotFunc",
        _t(
            "The `{0}` directive expects `Module.symbol` (exactly one dot). I got: `{1}`.",
            "Direktivet `{0}` förväntar `Module.symbol` (en punkt). Jag fick: `{1}`.",
            "La directiva `{0}` espera `Módulo.símbolo` (un punto). Recibí: `{1}`.",
        ),
    ),
    (
        "CliUrpFfiMapExpectedModuleFuncEquals",
        _t(
            "The `{0}` directive expects `Module.func=externalName`. I got: `{1}`.",
            "Direktivet `{0}` förväntar `Module.func=externtNamn`. Jag fick: `{1}`.",
            "La directiva `{0}` espera `Módulo.fun=externo`. Recibí: `{1}`.",
        ),
    ),
    (
        "CliUrpUnknownRewritePathKind",
        _t(
            "Unknown `rewrite` path kind `{0}`. Expected url, table, sequence, view, relation, cookie, style, or all.",
            "Okänd sökvägskind för `rewrite`: `{0}`. Tillåtet: url, table, sequence, view, relation, cookie, style, all.",
            "Clase de ruta `rewrite` desconocida: `{0}`. Válidas: url, table, sequence, view, relation, cookie, style, all.",
        ),
    ),
    (
        "CliUrpOnErrorNeedsQualifiedName",
        _t(
            "`onError` needs at least `Module.handler` or `A.B.handler`. I got: `{0}`.",
            "`onError` behöver minst `Modul.hanterare` eller `A.B.hanterare`. Jag fick: `{0}`.",
            "`onError` necesita al menos `Módulo.manejador` o `A.B.manejador`. Recibí: `{0}`.",
        ),
    ),
    (
        "CliUrpRewriteBadSyntax",
        _t(
            "I could not parse this `rewrite` line: `{0}`.",
            "Jag kunde inte tolka denna `rewrite`-rad: `{0}`.",
            "No pude analizar esta línea `rewrite`: `{0}`.",
        ),
    ),
    (
        "CliUrpAllowBadSyntax",
        _t(
            "`allow` needs exactly two words: `kind` then `pattern`. I got: `{0}`.",
            "`allow` kräver exakt två ord: `kind` sedan `pattern`. Jag fick: `{0}`.",
            "`allow` necesita dos palabras: `kind` y `pattern`. Recibí: `{0}`.",
        ),
    ),
    (
        "CliUrpDenyBadSyntax",
        _t(
            "`deny` needs exactly two words: `kind` then `pattern`. I got: `{0}`.",
            "`deny` kräver exakt två ord: `kind` sedan `pattern`. Jag fick: `{0}`.",
            "`deny` necesita dos palabras: `kind` y `pattern`. Recibí: `{0}`.",
        ),
    ),
    (
        "CliUrpUnknownFilterKind",
        _t(
            "Unknown filter kind `{0}` for `allow` / `deny`.",
            "Okänd filterkind `{0}` för `allow` / `deny`.",
            "Tipo de filtro `{0}` desconocido para `allow` / `deny`.",
        ),
    ),
    (
        "CliUrpLibraryNotFound",
        _t(
            "I could not find a library Ur/Web project for `{0}` (looked for `*.urp` and `lib.urp` next to that path).",
            "Jag hittade inget Ur/Web-biblioteksprojekt för `{0}` (sökte `*.urp` och `lib.urp`).",
            "No encontré proyecto de biblioteca Ur/Web para `{0}` (busqué `*.urp` y `lib.urp`).",
        ),
    ),
    (
        "CliDebuggerGdbStdoutClosed",
        _t(
            "The debugger backend closed its output stream (GDB/MI stdout ended).",
            "Debugger-backend stängde utdataströmmen (GDB/MI stdout slut).",
            "El backend del depurador cerró su salida (fin de stdout GDB/MI).",
        ),
    ),
    (
        "CliDebuggerGdbLineQueueMutexPoisoned",
        _t(
            "Internal error: GDB line queue mutex was poisoned.",
            "Internt fel: GDB-radkön mutex var poisoned.",
            "Error interno: el mutex de la cola de líneas GDB está envenenado.",
        ),
    ),
    (
        "CliDebuggerGdbMiReported",
        _t(
            "GDB/MI reported an error.\n\n{0}",
            "GDB/MI rapporterade ett fel.\n\n{0}",
            "GDB/MI informó un error.\n\n{0}",
        ),
    ),
    (
        "CliDebuggerSpawnMiBackendFailed",
        _t(
            "Could not start the debugger backend (`{0}`, mode `{1}`).\n\n{2}",
            "Kunde inte starta debugger-backend (`{0}`, läge `{1}`).\n\n{2}",
            "No pude iniciar el backend del depurador (`{0}`, modo `{1}`).\n\n{2}",
        ),
    ),
    (
        "CliDebuggerSetVariableNameNotSimpleCIdentifier",
        _t(
            "`setVariable` names must be a simple C identifier (letters, digits, underscore only).",
            "`setVariable`-namn måste vara ett enkelt C-identifierare.",
            "Los nombres de `setVariable` deben ser un identificador C simple.",
        ),
    ),
    (
        "CliDebuggerDapStaleVariablesReference",
        _t(
            "That variable reference is stale or unknown. Expand the scope again.",
            "Variablereferensen är inaktuell eller okänd. Expandera omfånget igen.",
            "Esa referencia de variable es obsoleta o desconocida. Vuelve a expandir el ámbito.",
        ),
    ),
    (
        "CliDebuggerDapVarCreateFailed",
        _t(
            "GDB `-var-create` did not return a variable name (MI parse failed).",
            "GDB `-var-create` returnerade inget variabelnamn (MI-tolkning misslyckades).",
            "GDB `-var-create` no devolvió un nombre de variable (fallo al interpretar MI).",
        ),
    ),
    (
        "CliDebuggerDapNotVariableContainer",
        _t(
            "That variable reference is not an expandable container.",
            "Den variablereferensen är inte en behållare som kan expanderas.",
            "Esa referencia no es un contenedor expandible.",
        ),
    ),
    (
        "CliDebuggerDapFieldNotFound",
        _t(
            "No child field matched `{0}` for `setVariable`.",
            "Inget barnfält matchade `{0}` för `setVariable`.",
            "Ningún campo hijo coincide con `{0}` para `setVariable`.",
        ),
    ),
    (
        "CliDebuggerDapNoLaunchBeforeConfigurationDone",
        _t(
            "Send `launch` or `attach` before `configurationDone` so the debugger can start.",
            "Skicka `launch` eller `attach` före `configurationDone` så debuggern kan starta.",
            "Envía `launch` o `attach` antes de `configurationDone` para iniciar el depurador.",
        ),
    ),
    (
        "CliDebuggerDapAttachFailed",
        _t(
            "Attaching to the process failed.\n\n{0}",
            "Att koppla till processen misslyckades.\n\n{0}",
            "No se pudo adjuntar al proceso.\n\n{0}",
        ),
    ),
    (
        "CliDebuggerDapLoadSymbolsFailed",
        _t(
            "Loading the program into the debugger failed.\n\n{0}",
            "Att ladda programmet i debuggern misslyckades.\n\n{0}",
            "Falló cargar el programa en el depurador.\n\n{0}",
        ),
    ),
    (
        "CliDebuggerDapRunInferiorFailed",
        _t(
            "Starting or continuing the inferior failed.\n\n{0}",
            "Att starta eller fortsätta inferioren misslyckades.\n\n{0}",
            "Fallo al iniciar o continuar el inferior.\n\n{0}",
        ),
    ),
    (
        "CliDebuggerDapGdbSessionMissing",
        _t(
            "The native debugger session is missing for `{0}`.",
            "Den inbyggda debuggersessionen saknas för `{0}`.",
            "Falta la sesión del depurador nativo para `{0}`.",
        ),
    ),
    (
        "CliDebuggerDapRequestBeforeLaunch",
        _t(
            "The debugger has not finished launching yet, so `{0}` cannot run.",
            "Debuggern har inte startat färdigt ännu, så `{0}` kan inte köras.",
            "El depurador aún no terminó de iniciarse; `{0}` no puede ejecutarse.",
        ),
    ),
    (
        "CliDebuggerDapReadSourceFailed",
        _t(
            "Could not read source file `{0}`.\n\n{1}",
            "Kunde inte läsa källfil `{0}`.\n\n{1}",
            "No pude leer el archivo fuente `{0}`.\n\n{1}",
        ),
    ),
    (
        "CliDebuggerDapDisassembleNeedsMemoryReference",
        _t(
            "`disassemble` needs `memoryReference` (a hex address, e.g. from `stackTrace.instructionPointerReference`).",
            "`disassemble` behöver `memoryReference` (hexadress, t.ex. från `stackTrace.instructionPointerReference`).",
            "`disassemble` necesita `memoryReference` (dirección hex, p. ej. de `stackTrace.instructionPointerReference`).",
        ),
    ),
    (
        "CliDebuggerDapSourceRequiresPathProperty",
        _t(
            "`source` requests need `Source.path` (sourceReference is not supported here).",
            "`source`-anrop behöver `Source.path` (sourceReference stöds inte här).",
            "Las peticiones `source` necesitan `Source.path` (aquí no hay `sourceReference`).",
        ),
    ),
    (
        "CliDebuggerDapAttachRequiresProcessId",
        _t(
            "`attach` requests need `processId`.",
            "`attach`-anrop behöver `processId`.",
            "Las peticiones `attach` necesitan `processId`.",
        ),
    ),
    (
        "CliDebuggerDapLaunchRequiresProgram",
        _t(
            "`launch` requests need `program`.",
            "`launch`-anrop behöver `program`.",
            "Las peticiones `launch` necesitan `program`.",
        ),
    ),
    (
        "CliDebuggerDapExceptionNoSignalDetailsThisThread",
        _t(
            "No signal details for this thread.",
            "Inga signaldetaljer för denna tråd.",
            "Sin detalles de señal para este hilo.",
        ),
    ),
    (
        "CliDebuggerDapExceptionNoInformation",
        _t(
            "No exception or signal information.",
            "Ingen undantags- eller signalinformation.",
            "Sin información de excepción o señal.",
        ),
    ),
    (
        "CliDebuggerDapBreakpointPendingAfterConfigurationDone",
        _t(
            "Breakpoint will install after `configurationDone` (native debug uses `.c` paths until CJR emits `#line` for `.ur`).",
            "Brytpunkten installeras efter `configurationDone` (inbyggd debug använder `.c`-vägar tills CJR ger `#line` för `.ur`).",
            "El punto de ruptura se instalará tras `configurationDone` (la depuración nativa usa rutas `.c` hasta que CJR emita `#line` para `.ur`).",
        ),
    ),
    (
        "CliDebuggerDapBreakpointGdbCouldNotSet",
        _t(
            "The debugger could not set this breakpoint (try the generated `.c` path or DWARF line mapping; `.ur` needs `#line` in CJR).",
            "Debuggern kunde inte sätta brytpunkten (prova genererad `.c`-väg eller DWARF-radkoppling; `.ur` behöver `#line` i CJR).",
            "El depurador no pudo fijar el punto de ruptura (prueba la ruta `.c` generada o el mapeo DWARF; `.ur` necesita `#line` en CJR).",
        ),
    ),
    (
        "CliDebuggerDapStoppedSignalLabel",
        _t(
            "Signal {0}",
            "Signal {0}",
            "Señal {0}",
        ),
    ),
    (
        "CliDebuggerDapExceptionDeliveredSignalDescription",
        _t(
            "Delivered signal {0}",
            "Levererad signal {0}",
            "Señal entregada {0}",
        ),
    ),
    (
        "CliDebuggerDapThreadDisplayName",
        _t(
            "Thread {0}",
            "Tråd {0}",
            "Hilo {0}",
        ),
    ),
    (
        "CliDebuggerDapScopeLocalsName",
        _t(
            "Locals",
            "Lokalt",
            "Locales",
        ),
    ),
    (
        "CliDebuggerDapFilterLabelFatalSignals",
        _t(
            "Fatal signals (SIGSEGV, SIGABRT, …)",
            "Fatala signaler (SIGSEGV, SIGABRT, …)",
            "Señales fatales (SIGSEGV, SIGABRT, …)",
        ),
    ),
    (
        "CliDebuggerDapFilterLabelAllSignals",
        _t(
            "Any signal (-catch-signal all)",
            "Valfri signal (-catch-signal all)",
            "Cualquier señal (-catch-signal all)",
        ),
    ),
    (
        "CliDebuggerDapFilterLabelCppThrow",
        _t(
            "C++ exceptions (-catch-throw)",
            "C++-undantag (-catch-throw)",
            "Excepciones C++ (-catch-throw)",
        ),
    ),
    (
        "CliDebuggerUnknownFlag",
        _t(
            "I do not recognize `{0}`.\n\nValid modes: `--dap`, `--gdb`, `--tty`. Try `ur-debugger --help`.",
            "Jag känner inte igen `{0}`.\n\nGiltiga lägen: `--dap`, `--gdb`, `--tty`. Se `ur-debugger --help`.",
            "No reconozco `{0}`.\n\nModos: `--dap`, `--gdb`, `--tty`. Prueba `ur-debugger --help`.",
        ),
    ),
    (
        "CliDebuggerMissingMode",
        _t(
            "Say which mode you want:\n"
            "  --dap   Debug Adapter Protocol on standard input/output\n"
            "  --gdb   Raw GDB/MI passthrough\n"
            "  --tty   Interactive GDB terminal\n\n"
            "Try: `ur-debugger --help`",
            "Ange läge: `--dap`, `--gdb` eller `--tty`. Kör `ur-debugger --help`.",
            "Indica el modo: `--dap`, `--gdb` o `--tty`. Ejecuta `ur-debugger --help`.",
        ),
    ),
    (
        "CliDebuggerCliDapStdioFailed",
        _t(
            "The Debug Adapter Protocol server on standard input/output failed.\n\n{0}",
            "Debug Adapter Protocol-servern på standard in/ut misslyckades.\n\n{0}",
            "El servidor del Debug Adapter Protocol por entrada/salida estándar falló.\n\n{0}",
        ),
    ),
    (
        "CliDebuggerCliTtyRequiresProgramPath",
        _t(
            "`--tty` needs a program path to debug after any `--run` flag (see `ur-debugger --help`).",
            "`--tty` behöver en programsökväg att debugga efter eventuell `--run`-flagga (se `ur-debugger --help`).",
            "`--tty` necesita la ruta del programa a depurar después de `--run` si aplica (ver `ur-debugger --help`).",
        ),
    ),
    (
        "CliDebuggerRunFailed",
        _t(
            "ur-debugger could not finish.\n\n{0}",
            "ur-debugger kunde inte slutföras.\n\n{0}",
            "ur-debugger no pudo terminar.\n\n{0}",
        ),
    ),
    (
        "CliDebuggerGdbSpawnFailed",
        _t(
            "I could not start GDB (is it installed and on `PATH`?).\n\n{0}",
            "Jag kunde inte starta GDB (installerat och på `PATH`?).\n\n{0}",
            "No pude iniciar GDB (¿está instalado y en `PATH`?).\n\n{0}",
        ),
    ),
    (
        "CliDebuggerGdbExecFailed",
        _t(
            "Replacing this process with GDB failed.\n\n{0}",
            "Att byta process till GDB misslyckades.\n\n{0}",
            "Falló ejecutar GDB con `exec`.\n\n{0}",
        ),
    ),
    (
        "CliDebuggerGdbExitedNonZero",
        _t(
            "GDB exited with status {0}.",
            "GDB avslutades med status {0}.",
            "GDB terminó con estado {0}.",
        ),
    ),
    (
        "CliDebuggerUsageBody",
        _t(
            "ur-debugger — native debugger (Debug Adapter Protocol + GDB)\n\n"
            "Modes:\n"
            "  --dap              DAP server on stdio (editors)\n"
            "  --gdb -- [args]    Passthrough: gdb -q --interpreter=mi3 [args]\n"
            "  --tty [--run] PROG [ARG ...]\n"
            "                     Interactive GDB: gdb -q [--ex run] --args PROG [ARG ...]\n\n"
            "Build with `ur-compile -debug` so the binary includes debug symbols.\n\n"
            "Examples:\n"
            "  ur-debugger --dap\n"
            "  ur-debugger --gdb -- -ex 'file ./myapp' -ex run\n"
            "  ur-debugger --tty --run ./myapp",
            "ur-debugger — inbyggd debugger (DAP + GDB). Se engelska hjälptexten ovan.",
            "ur-debugger — depurador nativo (DAP + GDB). Vea la ayuda en inglés arriba.",
        ),
    ),
    (
        "CliDevPreprocessWindowFailed",
        _t(
            "Development helper: could not read the preprocessor window.\n\n{0}",
            "Utvecklingshelper: kunde inte läsa preprocessorfönstret.\n\n{0}",
            "Herramienta de desarrollo: fallo al leer la ventana del preprocessador.\n\n{0}",
        ),
    ),
    (
        "CliPhaseIncompleteNoOutput",
        _t(
            "The compiler stopped: the {0} phase produced no output.\n\n"
            "There may be an earlier diagnostic — scroll up — or this may be an internal bug with a small repro.",
            "Kompilatorn stoppade: fasen {0} gav inget resultat.\n\n"
            "Leta efter tidigare diagnostik eller rapportera en bugg.",
            "El compilador se detuvo: la fase {0} no produjo salida.\n\n"
            "Busca diagnósticos anteriores o repórtalo con un ejemplo mínimo.",
        ),
    ),
    (
        "CliDebuggerGdbMiDriverLoopExhausted",
        _t(
            "Internal error: the GDB/MI driver loop finished without the usual completion token (please report this bug).",
            "Internt fel: GDB/MI-drivslingan avslutades utan förväntad sluttoken (rapportera gärna buggen).",
            "Error interno: el bucle del controlador GDB/MI terminó sin el token de finalización esperado (por favor repórtelo).",
        ),
    ),
    (
        "CliDebuggerDapStdioLoopExhausted",
        _t(
            "The Debug Adapter Protocol message loop reached its safety limit ({0} messages) without a clean end-of-file or shutdown. If this was a real session, please report a bug; otherwise the editor or client may be misbehaving.",
            "Debug Adapter Protocol-meddelandeslingan nådde säkerhetsgränsen ({0} meddelanden) utan ren filslut eller avstängning. Om det var en riktig session, rapportera buggen; annars kan klienten bete sig fel.",
            "El bucle de mensajes del Debug Adapter Protocol alcanzó el límite de seguridad ({0} mensajes) sin un fin de archivo limpio ni apagado. Si la sesión era legítima, repórtelo; si no, el editor o cliente puede estar mal.",
        ),
    ),
    (
        "CliBootRootNotFound",
        _t(
            "-boot requires the Ur/Web library tree (`lib/ur/basis.urs`). "
            "Set {0} to the checkout root, or run the compiler from that tree.",
            "-boot kräver Ur/Web-biblioteksträdet (`lib/ur/basis.urs`). "
            "Sätt {0} till checkouten, eller kör kompilatorn därifrån.",
            "-boot requiere el árbol de bibliotecas de Ur/Web (`lib/ur/basis.urs`). "
            "Establece {0} como la raíz del repositorio, o ejecuta el compilador desde ahí.",
        ),
    ),
    (
        "CliBootRootMissingBasis",
        _t(
            "-boot requires `lib/ur/basis.urs` at the provided root: {0}",
            "-boot kräver `lib/ur/basis.urs` i den angivna roten: {0}",
            "-boot requiere `lib/ur/basis.urs` en la raíz proporcionada: {0}",
        ),
    ),
    (
        "CompilerInternalBug",
        _t(
            "Internal compiler problem ({0}): {1}\n\n"
            "This is unexpected — your project may have triggered a compiler bug.\n"
            "Please report this with a small example if you can reproduce it.",
            "Internt kompilatproblem ({0}): {1}\n\n"
            "Detta är oväntat — ditt projekt kan ha utlöst en kompilatorbugg.\n"
            "Rapportera gärna med ett litet reproducerbart exempel.",
            "Problema interno del compilador ({0}): {1}\n\n"
            "Esto es inesperado — tu proyecto puede haber activado un error del compilador.\n"
            "Repórtalo con un ejemplo pequeño si puedes reproducirlo.",
        ),
    ),
    (
        "CliDatabaseBackendUrpRejected",
        _t(
            "I could not configure the database engine from the project file.\n\n{0}",
            "Jag kunde inte ställa in databasmotorn från projektfilen.\n\n{0}",
            "No pude configurar el motor de base de datos desde el archivo del proyecto.\n\n{0}",
        ),
    ),
]

for _name, _tpl in _CLI:
    add(_name, _tpl[0], _tpl[1], _tpl[2])
