(* Copyright (c) 2008-2012, Adam Chlipala
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

val socket = ".urweb_daemon"

exception Code of OS.Process.status

datatype flag_arity =
      ZERO of (unit -> unit)
    | ONE  of string * (string -> unit)
    | TWO  of string * string * (string * string -> unit)

fun parse_flags flag_info args =
    let
        fun search_pred flag0 =
            (* Remove preceding "-". *)
            let val flag0 = String.extract (flag0, 1, NONE)
            in
                fn (flag1, _, _) => flag0 = flag1
            end

        fun normalizeArg arg =
          case arg of
              "-h" => "-help"
            | "--h" => "-help"
            | "--help" => "-help"
            | _ => arg

        fun loop [] : string list = []
          | loop (arg :: args) =
            let
                val arg = normalizeArg arg
            in
                if String.isPrefix "-" arg then
                    case List.find (search_pred arg) flag_info of
                        NONE => raise Fail ("Unknown flag "^arg^", see -help")
                      | SOME x => exec x args
                else
                    arg :: loop args
            end

        and exec (_, ZERO f, _) args =
                (f (); loop args)
          | exec (_, ONE (_, f), _) (x :: args) =
                (f x; loop args)
          | exec (_, TWO (_, _, f), _) (x :: y :: args) =
                (f (x, y); loop args)
          | exec (flag, ONE _, _) [] =
                raise Fail ("Flag "^flag^" is missing an argument, see -help")
          | exec (flag, TWO _, _) [] =
                raise Fail ("Flag "^flag^" is missing two arguments, see -help")
          | exec (flag, TWO _, _) [_] =
                raise Fail ("Flag "^flag^" is missing an argument, see -help")
    in
        loop args
    end

fun usage flag_info =
    let
        val name = CommandLine.name ()

        fun print_desc NONE = print "\n"
          | print_desc (SOME s) = (print " : "; print s; print "\n")

        fun print_args (ZERO _) = ()
          | print_args (ONE (x, _)) = print (" " ^ x)
          | print_args (TWO (x, y, _)) = print (" " ^ x ^ " " ^ y)

        fun print_flag (flag, args, desc) =
            (print ("  -" ^ flag);
             print_args args;
             print_desc desc)
    in
        print "usage: \n";
        print ("  " ^ name ^ " new <project-name>\n");
        print ("  " ^ name ^ " new --lib <project-name>\n");
        print ("  " ^ name ^ " build\n");
        print ("  " ^ name ^ " fmt [options] [files...]\n");
        print ("  " ^ name ^ " install author/repo\n");
        print ("  " ^ name ^ " daemon [stop|start]\n");
        print ("  " ^ name ^ " [flag ...] project-name\n");
        print "Supported flags are:\n";
        app print_flag flag_info;
        raise Code OS.Process.success
    end



(* Encapsulate main invocation handler in a function, possibly to be called multiple times within a daemon. *)

exception DaemonExit

fun oneRun args =
    let
        val timing = ref false
        val tc = ref false
        val demo = ref (NONE : (string * bool) option)
        val tutorial = ref false
        val css = ref false

        val () = (Compiler.debug := false;
                  Elaborate.verbose := false;
                  Elaborate.dumpTypes := false;
                  Elaborate.dumpTypesOnError := false;
                  Elaborate.unifyMore := false;
                  Compiler.dumpSource := false;
                  Compiler.doIflow := false;
                  Demo.noEmacs := false;
                  Settings.setDebug false;
                  Compiler.partialBuild := NONE
                 )

        val () = Compiler.beforeC := MLton.GC.pack

        fun print_and_exit msg () =
            (print msg; print "\n";
             raise Code OS.Process.success)

        val printVersion = print_and_exit Config.versionString
        val printNumericVersion = print_and_exit Config.versionNumber
        fun printCCompiler () = print_and_exit (Settings.getCCompiler ()) ()
        val printCInclude = print_and_exit Config.includ

        fun printModuleOf fname =
            print_and_exit (Compiler.moduleOf fname) ()

        fun add_class (class, num) =
            case Int.fromString num of
                 NONE => raise Fail ("Invalid limit number '" ^ num ^ "'")
               | SOME n =>
                 if n < 0 then
                     raise Fail ("Invalid limit number '" ^ num ^ "'")
                 else
                     Settings.addLimit (class, n)

        fun set_true flag = ZERO (fn () => flag := true)
        fun call_true f = ZERO (fn () => f true)

        (* This is a function, and not simply a value, because it
         * is recursive in the help-flag. *)
        fun flag_info () = [
              ("help", ZERO (fn () => usage (flag_info ())),
                    SOME "print this overview"),
              ("version", ZERO printVersion,
                    SOME "print version number and exit"),
              ("numeric-version", ZERO printNumericVersion,
                    SOME "print numeric version number and exit"),
              ("css", set_true css,
                    SOME "print categories of CSS properties"),
              ("print-ccompiler", ZERO printCCompiler,
                    SOME "print C compiler and exit"),
              ("print-cinclude", ZERO printCInclude,
                    SOME "print directory of C headers and exit"),
              ("ccompiler", ONE ("<program>", Settings.setCCompiler),
                    SOME "set the C compiler to <program>"),
              ("demo", ONE ("<prefix>", fn prefix =>
                                demo := SOME (prefix, false)),
                    NONE),
              ("guided-demo", ONE ("<prefix>", fn prefix =>
                                demo := SOME (prefix, true)),
                    NONE),
              ("tutorial", set_true tutorial,
                    SOME "render HTML tutorials from .ur source files"),
              ("protocol", ONE ("[http|cgi|fastcgi|static]",
                                Settings.setProtocol),
                    SOME "set server protocol"),
              ("prefix", ONE ("<prefix>", Settings.setUrlPrefix),
                    SOME "set prefix used before all URI's"),
              ("db", ONE ("<string>", Settings.setDbstring o SOME),
                    SOME "database connection information"),
              ("dbms", ONE ("[sqlite|mysql|postgres]", Settings.setDbms),
                    SOME "select database engine"),
              ("debug", call_true Settings.setDebug,
                    SOME "save some intermediate C files"),
              ("verbose", ZERO (fn () =>
                                (Compiler.debug := true;
                                 Elaborate.verbose := true)),
                    NONE),
              ("timing", set_true timing,
                    SOME "time compilation phases"),
              ("tc", set_true tc,
                    SOME "stop after type checking"),
              ("dumpTypes", set_true Elaborate.dumpTypes,
                    SOME "print kinds and types"),
              ("dumpTypesOnError", set_true Elaborate.dumpTypesOnError,
                    SOME "print kinds and types if there is an error"),
              ("unifyMore", set_true Elaborate.unifyMore,
                    SOME "continue unification before reporting type error"),
              ("dumpSource", set_true Compiler.dumpSource,
                    SOME ("print source code of last intermediate program "^
                          "if there is an error")),
              ("dumpVerboseSource", ZERO (fn () =>
                                (Compiler.dumpSource := true;
                                 ElabPrint.debug := true;
                                 ExplPrint.debug := true;
                                 CorePrint.debug := true;
                                 MonoPrint.debug := true)),
                    NONE),
              ("output", ONE ("<file>", Settings.setExe o SOME),
                    SOME "output executable as <file>"),
              ("js", ONE ("<file>", Settings.setOutputJsFile o SOME),
                    SOME "serve JavaScript as <file>"),
              ("sql", ONE ("<file>", Settings.setSql o SOME),
                    SOME "output sql script as <file>"),
              ("endpoints", ONE ("<file>", Settings.setEndpoints o SOME),
                    SOME "output exposed URL endpoints in JSON as <file>"),
              ("static", call_true Settings.setStaticLinking,
                    SOME "enable static linking"),
              ("stop", ONE ("<phase>", Compiler.setStop),
                    SOME "stop compilation after <phase>"),
              ("path", TWO ("<name>", "<path>", Compiler.addPath),
                    SOME ("set path variable <name> to <path> for use in "^
                          ".urp files")),
              ("root", TWO ("<name>", "<path>",
                            (fn (name, path) =>
                                Compiler.addModuleRoot (path, name))),
                    SOME "prefix names of modules found in <path> with <name>"),
              ("boot", ZERO (fn () =>
                            (Compiler.enableBoot ();
                             Settings.setBootLinking true)),
                    SOME ("run from build tree and generate statically linked "^
                          "executables ")),
              ("sigfile", ONE ("<file>", Settings.setSigFile o SOME),
                    SOME "search for cryptographic signing keys in <file>"),
              ("iflow", set_true Compiler.doIflow,
                    NONE),
              ("sqlcache", call_true Settings.setSqlcache,
                    NONE),
              ("disablesqlstructurecheck", call_true Settings.setDisableSqlStructureCheck,
                    NONE),
              ("heuristic", ONE ("<h>", Sqlcache.setHeuristic),
                    NONE),
              ("moduleOf", ONE ("<file>", printModuleOf),
                    SOME "print module name of <file> and exit"),
              ("startLspServer", ZERO Lsp.startServer, SOME "Start Language Server Protocol server"),
              ("partialBuild", ONE ("<module>",
                                    (fn module =>
                                        Compiler.partialBuild := SOME module)),
               SOME "prefix names of modules found in <path> with <name>"),
              ("noEmacs", set_true Demo.noEmacs,
                    NONE),
              ("limit", TWO ("<class>", "<num>", add_class),
                    SOME "set resource usage limit for <class> to <num>"),
              ("explainEmbed", set_true JsComp.explainEmbed,
                    SOME ("explain errors about embedding of server-side "^
                          "values in client code"))
        ]

        val () = case args of
                     ["daemon", "stop"] => (OS.FileSys.remove socket handle OS.SysErr _ => ();
                                            raise DaemonExit)
                   | _ => ()

        val sources = parse_flags (flag_info ()) args

        val job =
            case sources of
                [file] => file
              | [] =>
                    raise Fail "No project specified, see -help"
              | files =>
                    raise Fail ("Multiple projects specified;"^
                                " only one is allowed.\nSpecified projects: "^
                                String.concatWith ", " files)
    in
        case (!css, !demo, !tutorial) of
            (true, _, _) =>
            (case Compiler.run Compiler.toCss job of
                 NONE => OS.Process.failure
               | SOME {Overall = ov, Classes = cl} =>
                 (app (print o Css.inheritableToString) ov;
                  print "\n";
                  app (fn (x, (ins, ots)) =>
                          (print x;
                           print " ";
                           app (print o Css.inheritableToString) ins;
                           app (print o Css.othersToString) ots;
                           print "\n")) cl;
                  OS.Process.success))
          | (_, SOME (prefix, guided), _) =>
            if Demo.make' {prefix = prefix, dirname = job, guided = guided} then
                OS.Process.success
            else
                OS.Process.failure
          | (_, _, true) => (Tutorial.make job;
                                OS.Process.success)
          | _ =>
            if !tc then
                (Compiler.check Compiler.toElaborate job;
                 if ErrorMsg.anyErrors () then
                     OS.Process.failure
                 else
                     OS.Process.success)
            else if !timing then
                (Compiler.time Compiler.toCjrize job;
                 OS.Process.success)
            else
                (if Compiler.compile job then
                     OS.Process.success
                 else
                     OS.Process.failure)
    end handle Code n => n

datatype projectKind = App | Library

val cursorMdContent =
    "# Ur/Web - Cursor AI Context\n" ^
    "\n" ^
    "This file provides context for AI assistants working with Ur/Web projects. " ^
    "For Cursor, you may copy this into `.cursor/rules/urweb.mdc` for automatic application to relevant files.\n" ^
    "\n" ^
    "## Language Overview\n" ^
    "\n" ^
    "- **Ur** is an ML/Haskell-style language: functional, pure, strict, statically typed\n" ^
    "- **Ur/Web** = Ur + web/SQL standard library\n" ^
    "- **Key guarantee:** Well-typed programs avoid code injection, invalid HTML, dead links, " ^
    "form/handler mismatches, invalid SQL, and marshaling errors\n" ^
    "\n" ^
    "## Core Syntax\n" ^
    "\n" ^
    "- **Types:** `transaction`, `page`, `source`, `xml`; records `{A = ..., B = ...}`; `con`, `val`, `datatype`\n" ^
    "- **Type params:** `::` = explicit, `:::` = implicit\n" ^
    "- **Comments:** `(* ... *)` (nestable)\n" ^
    "- **Modules:** `structure X : S = M`; files `M.ur` (impl), `M.urs` (signature, optional)\n" ^
    "\n" ^
    "## Web Constructs\n" ^
    "\n" ^
    "- **Page handler:** `fun main () : transaction page = return <xml>...</xml>`\n" ^
    "- **XML literals:** `<xml><body><h1>Hello</h1></body></xml>`; `{[e]}` for embedded expressions\n" ^
    "- **Forms:** `<form>`, `<textbox{#Field}/>`, `<checkbox{#B}/>`, `<submit action={handler}/>`\n" ^
    "- **Links:** `<a link={page}>`; **RPC:** `rpc` for client-to-server calls\n" ^
    "- **Client reactivity:** `source`, `signal`, `get`/`set`, `<dyn signal={...}>` for dynamic fragments\n" ^
    "\n" ^
    "## Database\n" ^
    "\n" ^
    "- **Tables:** `table t : {Id : int, Name : string} PRIMARY KEY Id`\n" ^
    "- **Sequences:** `sequence s`\n" ^
    "- **Views:** `view v = ...`\n" ^
    "- **Queries:** `query`, `insert`, `update`, `delete`\n" ^
    "\n" ^
    "## Project Structure\n" ^
    "\n" ^
    "- **`.urp` file:** Directives (`database`, `sql`, `prefix`, `rewrite`, etc.) + module list\n" ^
    "- **Module M** -> `M.ur` (required), `M.urs` (optional)\n" ^
    "- **URLs** map to `Module/page`; use `rewrite url` to shorten paths\n" ^
    "\n" ^
    "## Conventions\n" ^
    "\n" ^
    "- Module names: capital first letter (e.g. `Hello`, `Main`)\n" ^
    "- Entry point: `main` for the main page handler\n" ^
    "- Single-file projects: `foo.ur` without `foo.urp` -> implicit project named `foo`\n" ^
    "\n" ^
    "## Sources to Read\n" ^
    "\n" ^
    "- **Manual:** http://www.impredicative.com/ur/manual.pdf\n" ^
    "- **Project site:** http://www.impredicative.com/ur/\n" ^
    "- **Demo apps:** `demo/` in urweb source (hello, form, crud1, chat, etc.)\n" ^
    "- **Standard library:** `lib/ur/` (basis.urs, top.ur, etc.)\n"

val claudeMdContent =
    "# Ur/Web - Claude AI Context\n" ^
    "\n" ^
    "This file provides context for Claude and other AI assistants working with Ur/Web projects. " ^
    "Include it (e.g. via `@claude.md` or by reference) when editing Ur/Web code.\n" ^
    "\n" ^
    "## Language Overview\n" ^
    "\n" ^
    "- **Ur** is an ML/Haskell-style language: functional, pure, strict, statically typed\n" ^
    "- **Ur/Web** = Ur + web/SQL standard library\n" ^
    "- **Key guarantee:** Well-typed programs avoid code injection, invalid HTML, dead links, " ^
    "form/handler mismatches, invalid SQL, and marshaling errors\n" ^
    "\n" ^
    "## Core Syntax\n" ^
    "\n" ^
    "- **Types:** `transaction`, `page`, `source`, `xml`; records `{A = ..., B = ...}`; `con`, `val`, `datatype`\n" ^
    "- **Type params:** `::` = explicit, `:::` = implicit\n" ^
    "- **Comments:** `(* ... *)` (nestable)\n" ^
    "- **Modules:** `structure X : S = M`; files `M.ur` (impl), `M.urs` (signature, optional)\n" ^
    "\n" ^
    "## Web Constructs\n" ^
    "\n" ^
    "- **Page handler:** `fun main () : transaction page = return <xml>...</xml>`\n" ^
    "- **XML literals:** `<xml><body><h1>Hello</h1></body></xml>`; `{[e]}` for embedded expressions\n" ^
    "- **Forms:** `<form>`, `<textbox{#Field}/>`, `<checkbox{#B}/>`, `<submit action={handler}/>`\n" ^
    "- **Links:** `<a link={page}>`; **RPC:** `rpc` for client-to-server calls\n" ^
    "- **Client reactivity:** `source`, `signal`, `get`/`set`, `<dyn signal={...}>` for dynamic fragments\n" ^
    "\n" ^
    "## Database\n" ^
    "\n" ^
    "- **Tables:** `table t : {Id : int, Name : string} PRIMARY KEY Id`\n" ^
    "- **Sequences:** `sequence s`\n" ^
    "- **Views:** `view v = ...`\n" ^
    "- **Queries:** `query`, `insert`, `update`, `delete`\n" ^
    "\n" ^
    "## Project Structure\n" ^
    "\n" ^
    "- **`.urp` file:** Directives (`database`, `sql`, `prefix`, `rewrite`, etc.) + module list\n" ^
    "- **Module M** -> `M.ur` (required), `M.urs` (optional)\n" ^
    "- **URLs** map to `Module/page`; use `rewrite url` to shorten paths\n" ^
    "\n" ^
    "## Conventions\n" ^
    "\n" ^
    "- Module names: capital first letter (e.g. `Hello`, `Main`)\n" ^
    "- Entry point: `main` for the main page handler\n" ^
    "- Single-file projects: `foo.ur` without `foo.urp` -> implicit project named `foo`\n" ^
    "\n" ^
    "## Sources to Read\n" ^
    "\n" ^
    "- **Manual:** http://www.impredicative.com/ur/manual.pdf\n" ^
    "- **Project site:** http://www.impredicative.com/ur/\n" ^
    "- **Demo apps:** `demo/` in urweb source (hello, form, crud1, chat, etc.)\n" ^
    "- **Standard library:** `lib/ur/` (basis.urs, top.ur, etc.)\n"

(* --- Simple TOML parser (supports [section], key = "value", key = bare) --- *)

fun trimStr s =
    let
        val n = String.size s
        fun skipL i = if i >= n orelse not (Char.isSpace (String.sub (s, i))) then i else skipL (i+1)
        fun skipR i = if i < 0 orelse not (Char.isSpace (String.sub (s, i))) then i else skipR (i-1)
        val l = skipL 0
        val r = skipR (n-1)
    in if l > r then "" else String.substring (s, l, r-l+1) end

fun stripTomlQuotes s =
    let val n = String.size s
    in if n >= 2 andalso String.sub (s, 0) = #"\"" andalso String.sub (s, n-1) = #"\"" then
           String.substring (s, 1, n-2)
       else s end

(* Returns list of (section.key, value) string pairs *)
fun parseToml filename =
    let
        val f = TextIO.openIn filename
        fun loop (section, acc) =
            case TextIO.inputLine f of
                NONE => List.rev acc
              | SOME rawLine =>
                let
                    val line = trimStr rawLine
                    val n = String.size line
                in
                    if n = 0 orelse String.sub (line, 0) = #"#" then
                        loop (section, acc)
                    else if String.sub (line, 0) = #"[" andalso String.sub (line, n-1) = #"]" then
                        loop (trimStr (String.substring (line, 1, n-2)), acc)
                    else
                        let
                            fun findEq i = if i >= n then NONE
                                           else if String.sub (line, i) = #"=" then SOME i
                                           else findEq (i+1)
                        in
                            case findEq 0 of
                                NONE => loop (section, acc)
                              | SOME eq =>
                                let
                                    val key = trimStr (String.substring (line, 0, eq))
                                    val rawVal = trimStr (String.substring (line, eq+1, n-eq-1))
                                    val value = stripTomlQuotes rawVal
                                    val fullKey = if section = "" then key else section ^ "." ^ key
                                in loop (section, (fullKey, value) :: acc) end
                        end
                end
        val result = loop ("", [])
        val () = TextIO.closeIn f
    in result end

fun tomlGet entries key = Option.map #2 (List.find (fn (k, _) => k = key) entries)
fun tomlGetDef entries key def = case tomlGet entries key of NONE => def | SOME v => v

(* --- Project scaffolding --- *)

fun newProject kind name =
    let
        fun isValidChar c = Char.isAlphaNum c orelse c = #"_"
        val () =
            if String.size name = 0 then
                raise Fail "project name cannot be empty"
            else if not (Char.isAlpha (String.sub (name, 0))) then
                raise Fail ("project name must start with a letter: '" ^ name ^ "'")
            else if not (CharVector.all isValidChar name) then
                raise Fail ("project name must contain only letters, digits, or underscores: '" ^ name ^ "'")
            else ()
        val () =
            if OS.FileSys.access (name, []) then
                raise Fail ("'" ^ name ^ "' already exists")
            else ()
        val () = OS.FileSys.mkDir name
        val modName = str (Char.toUpper (String.sub (name, 0))) ^ String.extract (name, 1, NONE)
        fun writeFile (path, content) =
            let val f = TextIO.openOut path
            in  TextIO.output (f, content); TextIO.closeOut f end
        val () =
            case kind of
                App =>
                let
                    val () = writeFile (name ^ "/" ^ name ^ ".urp",
                                 "file /style/css/main.css style/css/main.css text/css\n" ^
                                 "\n" ^
                                 name ^ "\n")
                    val () = writeFile (name ^ "/" ^ name ^ ".ur",
                                 "fun main () : transaction page =\n" ^
                                 "  count <- source 0;\n" ^
                                 "  return <xml>\n" ^
                                 "    <head>\n" ^
                                 "      <title>" ^ modName ^ "</title>\n" ^
                                 "      <link rel=\"stylesheet\" href=\"/style/css/main.css\"/>\n" ^
                                 "    </head>\n" ^
                                 "    <body>\n" ^
                                 "      <h1>Counter</h1>\n" ^
                                 "      <dyn signal={n <- signal count;\n" ^
                                 "                   return <xml><p>Count: {[n]}</p></xml>}/>\n" ^
                                 "      <button onclick={fn _ => n <- get count; set count (n + 1)}>+</button>\n" ^
                                 "      <button onclick={fn _ => n <- get count; set count (n - 1)}>-</button>\n" ^
                                 "      <button onclick={fn _ => set count 0}>Reset</button>\n" ^
                                 "    </body>\n" ^
                                 "  </xml>\n")
                    val () = OS.FileSys.mkDir (name ^ "/style")
                    val () = OS.FileSys.mkDir (name ^ "/style/scss")
                    val () = OS.FileSys.mkDir (name ^ "/style/css")
                    val () = writeFile (name ^ "/style/scss/main.scss",
                                 "$primary: #3498db;\n" ^
                                 "$bg:      #f5f5f5;\n" ^
                                 "$text:    #333;\n" ^
                                 "\n" ^
                                 "body {\n" ^
                                 "  font-family: sans-serif;\n" ^
                                 "  background: $bg;\n" ^
                                 "  color: $text;\n" ^
                                 "  margin: 0;\n" ^
                                 "  padding: 2rem;\n" ^
                                 "}\n" ^
                                 "\n" ^
                                 "h1 {\n" ^
                                 "  color: $primary;\n" ^
                                 "  margin-bottom: 1rem;\n" ^
                                 "}\n" ^
                                 "\n" ^
                                 "button {\n" ^
                                 "  background: $primary;\n" ^
                                 "  color: white;\n" ^
                                 "  border: none;\n" ^
                                 "  padding: 0.5rem 1rem;\n" ^
                                 "  margin: 0.25rem;\n" ^
                                 "  cursor: pointer;\n" ^
                                 "  border-radius: 4px;\n" ^
                                 "  font-size: 1rem;\n" ^
                                 "\n" ^
                                 "  &:hover {\n" ^
                                 "    opacity: 0.85;\n" ^
                                 "  }\n" ^
                                 "}\n" ^
                                 "\n" ^
                                 "p {\n" ^
                                 "  font-size: 1.5rem;\n" ^
                                 "}\n")
                    (* Pre-compiled CSS so the project works immediately without sass *)
                    val () = writeFile (name ^ "/style/css/main.css",
                                 "body {\n" ^
                                 "  font-family: sans-serif;\n" ^
                                 "  background: #f5f5f5;\n" ^
                                 "  color: #333;\n" ^
                                 "  margin: 0;\n" ^
                                 "  padding: 2rem;\n" ^
                                 "}\n" ^
                                 "\n" ^
                                 "h1 {\n" ^
                                 "  color: #3498db;\n" ^
                                 "  margin-bottom: 1rem;\n" ^
                                 "}\n" ^
                                 "\n" ^
                                 "button {\n" ^
                                 "  background: #3498db;\n" ^
                                 "  color: white;\n" ^
                                 "  border: none;\n" ^
                                 "  padding: 0.5rem 1rem;\n" ^
                                 "  margin: 0.25rem;\n" ^
                                 "  cursor: pointer;\n" ^
                                 "  border-radius: 4px;\n" ^
                                 "  font-size: 1rem;\n" ^
                                 "}\n" ^
                                 "\n" ^
                                 "button:hover {\n" ^
                                 "  opacity: 0.85;\n" ^
                                 "}\n" ^
                                 "\n" ^
                                 "p {\n" ^
                                 "  font-size: 1.5rem;\n" ^
                                 "}\n")
                    val () = writeFile (name ^ "/urweb.toml",
                                 "[package]\n" ^
                                 "name = \"" ^ name ^ "\"\n" ^
                                 "kind = \"app\"\n" ^
                                 "\n" ^
                                 "[build]\n" ^
                                 "entry     = \"" ^ name ^ "\"\n" ^
                                 "db        = \"sqlite\"\n" ^
                                 "ccompiler = \"gcc\"\n" ^
                                 "boot      = false\n" ^
                                 "\n" ^
                                 "[style]\n" ^
                                 "scss = \"style/scss/main.scss\"\n" ^
                                 "css  = \"style/css/main.css\"\n")
                in () end
              | Library =>
                let
                    val () = writeFile (name ^ "/" ^ name ^ ".urp", name ^ "\n")
                    val () = writeFile (name ^ "/" ^ name ^ ".urs",
                                 "val add : int -> int -> int\n" ^
                                 "val greet : string -> string\n")
                    val () = writeFile (name ^ "/" ^ name ^ ".ur",
                                 "fun add (x : int) (y : int) : int = x + y\n" ^
                                 "\n" ^
                                 "fun greet (name : string) : string = \"Hello, \" ^ name ^ \"!\"\n")
                    val () = writeFile (name ^ "/urweb.toml",
                                 "[package]\n" ^
                                 "name = \"" ^ name ^ "\"\n" ^
                                 "kind = \"lib\"\n" ^
                                 "\n" ^
                                 "[build]\n" ^
                                 "entry = \"" ^ name ^ "\"\n" ^
                                 "boot  = false\n")
                in () end
        val () = writeFile (name ^ "/cursor.md", cursorMdContent)
        val () = writeFile (name ^ "/claude.md", claudeMdContent)
        val () = writeFile (name ^ "/.gitignore",
                    "# Compiled executables\n" ^
                    "*.exe\n" ^
                    "\n" ^
                    "# SQLite databases and generated SQL schemas\n" ^
                    "*.db\n" ^
                    "*.sql\n" ^
                    "\n" ^
                    "# Urweb daemon socket\n" ^
                    ".urweb_daemon\n" ^
                    (case kind of
                         App => "\n# Compiled CSS (regenerated by 'urweb build' from style/scss/)\nstyle/css/*.css\n"
                       | Library => ""))
        val gitInitialized = OS.Process.isSuccess
                                 (OS.Process.system
                                      ("git -C " ^ name ^ " init -q 2>/dev/null"))
        val kindStr = case kind of App => "app" | Library => "library"
        val () = (print ("Created " ^ kindStr ^ " '" ^ name ^ "'\n");
                  print "\n";
                  print ("  " ^ name ^ "/urweb.toml\n");
                  print ("  " ^ name ^ "/" ^ name ^ ".urp\n");
                  print ("  " ^ name ^ "/" ^ name ^ ".ur\n");
                  (case kind of Library => print ("  " ^ name ^ "/" ^ name ^ ".urs\n") | App => ());
                  (case kind of
                       App => (print ("  " ^ name ^ "/style/scss/main.scss\n");
                               print ("  " ^ name ^ "/style/css/main.css\n"))
                     | Library => ());
                  print ("  " ^ name ^ "/cursor.md\n");
                  print ("  " ^ name ^ "/claude.md\n");
                  print ("  " ^ name ^ "/.gitignore\n");
                  print "\n";
                  (if gitInitialized then print "  (initialized git repository)\n\n" else ());
                  print ("Build:  cd " ^ name ^ " && urweb build\n"))
    in
        OS.Process.success
    end
    handle Fail s => (print ("error: " ^ s ^ "\n"); OS.Process.failure)
         | OS.SysErr (s, _) => (print ("error: " ^ s ^ "\n"); OS.Process.failure)

(* --- urweb fmt: format .ur and .urs files --- *)

fun fmtCommand args =
    let
        (* Normalize --flag to -flag for fmt flags *)
        val args = List.map (fn a => if String.isPrefix "--" a then "-" ^ String.extract (a, 2, NONE) else a) args
        val check = ref false
        val width = ref 80
        val fmtFlagInfo = [
            ("help", ZERO (fn () =>
                (print "urweb fmt [options] [files...]\n";
                 print "  If no files: format all .ur/.urs in project (from urweb.toml)\n";
                 print "  Otherwise: format the given files. Comments preserved.\n";
                 print "  -check: check only; exit 1 if would reformat (CI mode)\n";
                 print "  -w N, --width N: line width (default 80)\n";
                 OS.Process.exit OS.Process.success)), SOME "show fmt help"),
            ("check", ZERO (fn () => check := true), SOME "check only; exit 1 if would reformat"),
            ("w", ONE ("<n>", fn s => width := valOf (Int.fromString s) handle Option => ()),
             SOME "line width (default 80)"),
            ("width", ONE ("<n>", fn s => width := valOf (Int.fromString s) handle Option => ()),
             SOME "line width (default 80)")
        ]
        val files = parse_flags fmtFlagInfo args
        val wid = !width
        fun formatOne checkMode fname =
            let
                val isUrs = String.isSuffix ".urs" fname
                val isUr = String.isSuffix ".ur" fname andalso not isUrs
            in
                if not (isUr orelse isUrs) then
                    (print ("error: " ^ fname ^ " is not a .ur or .urs file\n"); false)
                else if not (OS.FileSys.access (fname, [OS.FileSys.A_READ])) then
                    (print ("error: " ^ fname ^ " not found\n"); false)
                else
                    let
                        val outOpt = if isUr then Format.formatUrToString fname wid
                                     else Format.formatUrsToString fname wid
                    in
                        case outOpt of
                            NONE => (print ("error: could not parse " ^ fname ^ "\n"); false)
                          | SOME out =>
                                if checkMode then
                                    let val inf = FileIO.txtOpenIn fname
                                        val orig = TextIO.inputAll inf
                                        val () = TextIO.closeIn inf
                                    in
                                        if orig = out then true
                                        else (print ("would reformat " ^ fname ^ "\n"); false)
                                    end
                                    handle _ => (print ("error reading " ^ fname ^ "\n"); false)
                                else
                                    let val outf = TextIO.openOut fname
                                    in TextIO.output (outf, out); TextIO.closeOut outf; true end
                    end
            end
        fun doFiles checkMode files =
            case files of
                [] => (print "error: no files specified\n"; false)
              | fs => List.all (formatOne checkMode) fs
    in
        if List.null files then
            (* Project mode: read urweb.toml, get entry, parse .urp, format all .ur/.urs *)
            let
                val tomlFile = "urweb.toml"
                val () = if not (OS.FileSys.access (tomlFile, [OS.FileSys.A_READ])) then
                            raise Fail "urweb.toml not found; run from project directory or specify files"
                         else ()
                val entries = parseToml tomlFile
                val entry = tomlGetDef entries "build.entry" ""
                val () = if entry = "" then raise Fail "urweb.toml: [build] entry is required" else ()
                val urpFile = entry ^ ".urp"
                val () = if not (OS.FileSys.access (urpFile, [OS.FileSys.A_READ])) then
                            raise Fail ("project .urp not found: " ^ urpFile)
                         else ()
                val jobOpt = Compiler.run (Compiler.transform Compiler.parseUrp "parseUrp") entry
                val job = case jobOpt of NONE => raise Fail "could not parse .urp"
                                       | SOME j => j
                val sources = #sources job
                val filesToFormat = List.concat (List.map (fn m =>
                    let val ur = m ^ ".ur"
                        val urs = m ^ ".urs"
                    in
                        (if OS.FileSys.access (ur, []) then [ur] else []) @
                        (if OS.FileSys.access (urs, []) then [urs] else [])
                    end) sources)
            in
                if List.null filesToFormat then
                    (print "no .ur or .urs files found\n"; true)
                else
                    doFiles (!check) filesToFormat
            end
        else
            doFiles (!check) files
    end
    handle Fail s => (print ("error: " ^ s ^ "\n"); false)

(* --- urweb build: reads urweb.toml, compiles SCSS, then compiles the project --- *)

fun buildProject () =
    let
        val tomlFile = "urweb.toml"
        val () =
            if not (OS.FileSys.access (tomlFile, [OS.FileSys.A_READ])) then
                raise Fail ("urweb.toml not found in current directory\n" ^
                            "Run 'urweb new <name>' to create a project, then 'cd <name> && urweb build'")
            else ()
        val entries = parseToml tomlFile
        val kind   = tomlGetDef entries "package.kind"  "app"
        val entry  = tomlGetDef entries "build.entry"   ""
        val db     = tomlGetDef entries "build.db"      "sqlite"
        val cc     = tomlGetDef entries "build.ccompiler" ""
        val boot   = tomlGetDef entries "build.boot"    "false" = "true"
        val scss   = tomlGet    entries "style.scss"
        val css    = tomlGet    entries "style.css"
        val () = if entry = "" then raise Fail "urweb.toml: [build] entry is required" else ()
        val () = if boot then (Compiler.enableBoot (); Settings.setBootLinking true) else ()
        (* Compile SCSS -> CSS *)
        val () =
            case (scss, css) of
                (SOME scssPath, SOME cssPath) =>
                let
                    val hasSass  = OS.Process.isSuccess (OS.Process.system "which sass  >/dev/null 2>&1")
                    val hasSassc = OS.Process.isSuccess (OS.Process.system "which sassc >/dev/null 2>&1")
                    val cmd =
                        if hasSass  then "sass "  ^ scssPath ^ ":" ^ cssPath ^ " --no-source-map --style=expanded"
                        else if hasSassc then "sassc " ^ scssPath ^ " " ^ cssPath
                        else raise Fail ("sass not found; install sass or sassc to compile SCSS\n" ^
                                         "(or remove [style] from urweb.toml to skip)")
                    val () = print ("  Compiling SCSS...\n")
                in
                    if not (OS.Process.isSuccess (OS.Process.system cmd)) then
                        raise Fail "SCSS compilation failed"
                    else ()
                end
              | _ => ()
        (* Compile the Ur/Web project *)
        val isLib = kind = "lib"
        val args =
            (if cc <> "" then ["-ccompiler", cc] else []) @
            (if isLib then
                 ["-tc", entry]
             else
                 ["-dbms", db, "-db", entry ^ ".db", "-sql", entry ^ ".sql", entry])
        val () = print ("  " ^ (if isLib then "Type-checking" else "Building") ^ " " ^ entry ^ "...\n")
    in
        oneRun args
    end
    handle Fail s => (print ("error: " ^ s ^ "\n"); OS.Process.failure)
         | OS.SysErr (s, _) => (print ("error: " ^ s ^ "\n"); OS.Process.failure)

(* --- urweb install: add a github package as a git submodule and link it --- *)

fun installPackage spec =
    let
        (* Extract the last non-empty path component *)
        fun lastComp s =
            case List.rev (List.filter (fn p => p <> "")
                               (String.fields (fn c => c = #"/") s)) of
                [] => s
              | last :: _ => last

        fun stripDotGit s =
            if String.size s >= 4
               andalso String.substring (s, String.size s - 4, 4) = ".git"
            then String.substring (s, 0, String.size s - 4)
            else s

        fun hasPrefix pre s =
            String.size s >= String.size pre
            andalso String.substring (s, 0, String.size pre) = pre

        val (url, repoName) =
            let val s = stripDotGit spec in
                if hasPrefix "/" s orelse hasPrefix "./" s then
                    (* Local filesystem path for testing *)
                    (s, lastComp s)
                else if hasPrefix "https://" s orelse hasPrefix "http://" s then
                    (s, lastComp s)
                else if hasPrefix "github.com/" s then
                    ("https://" ^ s, lastComp s)
                else
                    (* "author/repo" GitHub shorthand *)
                    case String.fields (fn c => c = #"/") s of
                        [_, repo] => ("https://github.com/" ^ s, repo)
                      | _ => raise Fail ("Cannot parse package: '" ^ spec ^ "'\n" ^
                                         "  Expected:  author/repo\n" ^
                                         "             github.com/author/repo\n" ^
                                         "             https://github.com/author/repo")
            end

        (* Must be run from a project directory *)
        val () =
            if not (OS.FileSys.access ("urweb.toml", [OS.FileSys.A_READ])) then
                raise Fail "urweb.toml not found; run 'urweb install' from your project directory"
            else ()

        val projEntries = parseToml "urweb.toml"
        val projEntry   = tomlGetDef projEntries "build.entry" ""
        val ()          = if projEntry = "" then
                              raise Fail "urweb.toml: [build] entry not found"
                          else ()
        val urpFile     = projEntry ^ ".urp"
        val ()          = if not (OS.FileSys.access (urpFile, [OS.FileSys.A_READ])) then
                              raise Fail ("Project .urp not found: " ^ urpFile)
                          else ()

        val libDir     = "lib"
        val installDir = libDir ^ "/" ^ repoName

        val () =
            if not (OS.FileSys.access (libDir, [])) then OS.FileSys.mkDir libDir else ()

        val () =
            if OS.FileSys.access (installDir, []) then
                raise Fail ("'" ^ repoName ^ "' is already installed at " ^ installDir)
            else ()

        (* Clone as a git submodule.
           Local paths need protocol.file.allow=always (blocked by default since git 2.38) *)
        val isLocalPath = hasPrefix "/" url orelse hasPrefix "./" url
        val gitCmd = if isLocalPath
                     then "git -c protocol.file.allow=always submodule add " ^ url ^ " " ^ installDir
                     else "git submodule add " ^ url ^ " " ^ installDir
        val () = print ("  Fetching " ^ repoName ^ " from " ^ url ^ "...\n")
        val () =
            if not (OS.Process.isSuccess (OS.Process.system gitCmd)) then
                raise Fail "git submodule add failed"
            else ()

        (* Determine the library path to embed in the .urp directive.
           - If the package has urweb.toml with a non-empty entry, use installDir/entry
           - Otherwise fall back to installDir alone (urweb's libify will try
             installDir.urp then installDir/lib.urp automatically) *)
        val libraryArg =
            let val pkgToml = installDir ^ "/urweb.toml" in
                if OS.FileSys.access (pkgToml, [OS.FileSys.A_READ]) then
                    let val e = tomlGetDef (parseToml pkgToml) "build.entry" ""
                    in if e <> "" then installDir ^ "/" ^ e else installDir end
                else
                    installDir
            end

        val libraryLine = "library " ^ libraryArg

        (* Read .urp lines, check for duplicates *)
        fun readLines path =
            let val f = TextIO.openIn path
                fun loop acc =
                    case TextIO.inputLine f of NONE => List.rev acc | SOME l => loop (l :: acc)
                val result = loop []
                val () = TextIO.closeIn f
            in result end

        val ()  = if List.exists (fn l => trimStr l = libraryLine) (readLines urpFile) then
                      raise Fail (repoName ^ " is already linked in " ^ urpFile)
                  else ()

        (* Patch .urp: insert library directive before the last non-blank line (main module) *)
        val () =
            let
                val lines = readLines urpFile
                fun isBlank s = CharVector.all Char.isSpace s
                fun lastNonBlank lines =
                    let val n = length lines
                        fun go i = if i < 0 then NONE
                                   else if not (isBlank (List.nth (lines, i))) then SOME i
                                   else go (i - 1)
                    in go (n - 1) end
                val newLines =
                    case lastNonBlank lines of
                        NONE   => lines @ [libraryLine ^ "\n"]
                      | SOME i => List.take (lines, i) @
                                  [libraryLine ^ "\n"] @
                                  List.drop (lines, i)
                val out = TextIO.openOut urpFile
                val ()  = List.app (fn l => TextIO.output (out, l)) newLines
                val ()  = TextIO.closeOut out
            in () end

        (* Patch urweb.toml: add entry to [dependencies] section *)
        val () =
            let
                val lines   = readLines "urweb.toml"
                val depLine = repoName ^ " = \"" ^ libraryArg ^ "\"\n"
                val hasDeps = List.exists (fn l => trimStr l = "[dependencies]") lines
                val newLines =
                    if hasDeps then
                        let fun ins [] = []
                              | ins (l :: rest) =
                                if trimStr l = "[dependencies]" then l :: depLine :: rest
                                else l :: ins rest
                        in ins lines end
                    else
                        lines @ ["\n[dependencies]\n", depLine]
                val out = TextIO.openOut "urweb.toml"
                val ()  = List.app (fn l => TextIO.output (out, l)) newLines
                val ()  = TextIO.closeOut out
            in () end

        val () = (print "\n";
                  print ("  Installed " ^ repoName ^ "\n");
                  print ("  Path:     " ^ installDir ^ "\n");
                  print ("  Linked:   " ^ libraryLine ^ "\n");
                  print ("  Updated:  " ^ urpFile ^ ", urweb.toml\n"))
    in
        OS.Process.success
    end
    handle Fail s => (print ("error: " ^ s ^ "\n"); OS.Process.failure)
         | OS.SysErr (s, _) => (print ("error: " ^ s ^ "\n"); OS.Process.failure)

fun send (sock, s) =
    let
        val n = Socket.sendVec (sock, Word8VectorSlice.full (MLton.Word8Vector.fromPoly (Vector.map (Word8.fromInt o ord) (MLton.CharVector.toPoly s))))
    in
        if n >= size s then
            ()
        else
            send (sock, String.extract (s, n, NONE))
    end

fun startDaemon () =
    if OS.FileSys.access (socket, []) then
        (print ("It looks like a daemon is already listening in this directory,\n"
                ^ "though it's possible a daemon died without cleaning up its socket.\n");
         OS.Process.exit OS.Process.failure)
    else case Posix.Process.fork () of
             SOME _ => ()
           | NONE =>
             let
                 val () = Elaborate.incremental := true
                 val listen = UnixSock.Strm.socket ()

                 fun loop () =
                     let
                         val (sock, _) = Socket.accept listen

                         fun loop' (buf, args) =
                             let
                                 val s = if CharVector.exists (fn ch => ch = #"\n") buf then
                                             ""
                                         else
                                             MLton.CharVector.fromPoly (Vector.map (chr o Word8.toInt) (MLton.Word8Vector.toPoly (Socket.recvVec (sock, 1024))))
                                 val s = buf ^ s
                                 val (befor, after) = Substring.splitl (fn ch => ch <> #"\n") (Substring.full s)
                             in
                                 if Substring.isEmpty after then
                                     loop' (s, args)
                                 else
                                     let
                                         val cmd = Substring.string befor
                                         val rest = Substring.string (Substring.slice (after, 1, NONE))
                                     in
                                         case cmd of
                                             "" =>
                                             (case args of
                                                  ["stop", "daemon"] =>
                                                  (((Socket.close listen;
                                                     OS.FileSys.remove socket) handle OS.SysErr _ => ());
                                                   OS.Process.exit OS.Process.success)
                                                | _ =>
                                                  let
                                                      val success = (oneRun (rev args) handle DaemonExit => OS.Process.exit OS.Process.success)
                                                                    handle ex => (print "unhandled exception:\n";
                                                                                  print (General.exnMessage ex ^ "\n");
                                                                                  OS.Process.failure)
                                                  in
                                                      TextIO.flushOut TextIO.stdOut;
                                                      TextIO.flushOut TextIO.stdErr;
                                                      send (sock, if OS.Process.isSuccess success then
                                                                      "\001"
                                                                  else
                                                                      "\002")
                                                  end)
                                           | _ => loop' (rest, cmd :: args)
                                     end
                             end handle OS.SysErr _ => ()

                         fun redirect old =
                             Posix.IO.dup2 {old = valOf (Posix.FileSys.iodToFD (Socket.ioDesc sock)),
                                            new = old}

                         val oldStdout = Posix.IO.dup Posix.FileSys.stdout
                         val oldStderr = Posix.IO.dup Posix.FileSys.stderr
                     in
                         (* Redirect the daemon's output to the socket. *)
                         redirect Posix.FileSys.stdout;
                         redirect Posix.FileSys.stderr;

                         loop' ("", []);
                         Socket.close sock;

                         Posix.IO.dup2 {old = oldStdout, new = Posix.FileSys.stdout};
                         Posix.IO.dup2 {old = oldStderr, new = Posix.FileSys.stderr};
                         Posix.IO.close oldStdout;
                         Posix.IO.close oldStderr;

                         Settings.reset ();
                         MLton.GC.pack ();
                         loop ()
                     end
             in
                 OS.Process.atExit (fn () => OS.FileSys.remove socket);
                 Socket.bind (listen, UnixSock.toAddr socket);
                 Socket.listen (listen, 1);
                 loop ()
             end

fun oneCommandLine args =
    let
        val sock = UnixSock.Strm.socket ()

        fun wait () =
            let
                val v = Socket.recvVec (sock, 1024)
            in
                if Word8Vector.length v = 0 then
                    OS.Process.failure
                else
                    let
                        val s = MLton.CharVector.fromPoly (Vector.map (chr o Word8.toInt) (MLton.Word8Vector.toPoly v))
                        val last = Word8Vector.sub (v, Word8Vector.length v - 1)
                        val (rc, s) = if last = Word8.fromInt 1 then
                                          (SOME OS.Process.success, String.substring (s, 0, size s - 1))
                                      else if last = Word8.fromInt 2 then
                                          (SOME OS.Process.failure, String.substring (s, 0, size s - 1))
                                      else
                                          (NONE, s)
                    in
                        print s;
                        case rc of
                            NONE => wait ()
                          | SOME rc => rc
                    end
            end handle OS.SysErr _ => OS.Process.failure
    in
        if Socket.connectNB (sock, UnixSock.toAddr socket)
           orelse not (List.null (#wrs (Socket.select {rds = [],
                                                       wrs = [Socket.sockDesc sock],
                                                       exs = [],
                                                       timeout = SOME (Time.fromSeconds 1)}))) then
            (app (fn arg => send (sock, arg ^ "\n")) args;
             send (sock, "\n");
             wait ())
        else
            (OS.FileSys.remove socket;
             raise OS.SysErr ("", NONE))
    end handle OS.SysErr _ => oneRun args handle DaemonExit => OS.Process.success
            
val () = (Globals.setResetTime ();
          case CommandLine.arguments () of
              ["daemon", "start"] => startDaemon ()
            | ["daemon", "restart"] =>
              (ignore (oneCommandLine ["daemon", "stop"]);
               startDaemon ())
            | ["-startLspServer"] =>
              ( Lsp.startServer ()
              ; OS.Process.exit OS.Process.success)
            | ("build" :: _) => OS.Process.exit (buildProject ())
            | ["install"] =>
              (print "error: 'install' requires a package\n";
               print "usage: urweb install author/repo\n";
               print "       urweb install github.com/author/repo\n";
               print "       urweb install https://github.com/author/repo\n";
               OS.Process.exit OS.Process.failure)
            | ("install" :: pkg :: _) => OS.Process.exit (installPackage pkg)
            | ("fmt" :: args) => OS.Process.exit (if fmtCommand args then OS.Process.success else OS.Process.failure)
            | ("new" :: args) =>
              let
                  val isLib = List.exists (fn a => a = "--lib") args
                  val names = List.filter (fn a => size a = 0 orelse String.sub (a, 0) <> #"-") args
                  val kind = if isLib then Library else App
              in
                  case names of
                      [] => (print "error: 'new' requires a project name\n";
                             print "usage: urweb new [--lib] <project-name>\n";
                             OS.Process.exit OS.Process.failure)
                    | name :: _ => OS.Process.exit (newProject kind name)
              end
            | args => OS.Process.exit (oneCommandLine args))
