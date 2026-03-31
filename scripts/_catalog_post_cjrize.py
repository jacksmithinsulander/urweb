# Executed by gen_diagnostic_catalog.py — entries after Cjrize* that must precede CLI catalog.


def _p(en: str, sv: str | None = None, es: str | None = None) -> tuple[str, str, str]:
    return (en, sv or en, es or en)


_POST: list[tuple[str, tuple[str, str, str]]] = [
    (
        "CorifyUnknownTypeNameInModulePath",
        _p(
            "While lowering types for JavaScript/export I could not resolve the name `{0}` on this module path.\n\n"
            "Check `open`, `structure`, and qualified paths — the name may be out of scope.",
        ),
    ),
    (
        "CorifyUnknownPatternConstructorId",
        _p(
            "Internal pattern lowering saw constructor id `{0}` with no matching datatype entry — this usually follows an earlier elaboration error.",
        ),
    ),
    (
        "CorifyUnknownDataConstructorInModulePath",
        _p(
            "Pattern uses constructor `{0}` but it is not defined on the structure path you wrote.\n\n"
            "Spell the constructor like in its `datatype` declaration, or fix the module prefix.",
        ),
    ),
    (
        "JscompInternalStrcatInvariant",
        _p(
            "Internal JavaScript lowering invariant failed while folding string concatenation: {0}.\n\n"
            "If you see this on a small program, please report it as a compiler bug.",
        ),
    ),
    (
        "JscompUnurlifyUnknownType",
        _p(
            "Client JavaScript generation does not know how to `unurlify` this type yet.",
        ),
    ),
    (
        "JscompUnsupportedFfiValueInJs",
        _p(
            "The FFI value `{0}` at {1} has no `jsFunc` mapping, so client JavaScript cannot embed it cleanly.",
        ),
    ),
    (
        "JscompUnsupportedFfiCallInJs",
        _p(
            "Call `{0}.{1}` at {2} is not mapped for client JavaScript (needs `jsFunc` in the project file).",
        ),
    ),
    (
        "JscompUnknownUnaryOperatorInJs",
        _p(
            "Client JavaScript does not define unary `{0}` — use a supported operator or avoid this form in `<script>` code.",
        ),
    ),
    (
        "JscompUnknownBinaryOperatorInJs",
        _p(
            "Client JavaScript does not define binary `{0}` — check the embeddable subset in the manual.",
        ),
    ),
    (
        "JscompClientConstructUnsupportedInJs",
        _p(
            "This construct ({0}) cannot run on the client as compiled JavaScript — keep database, RPC, or server-only effects on the server.",
        ),
    ),
    (
        "SideGetenvNotCompileTimeString",
        _p(
            "`Basis.getenv` needs a compile-time string literal for the variable name at {0} so the compiler can record dependencies.",
        ),
    ),
    (
        "HintSideGetenvNotCompileTimeString",
        _p(
            "Write `Basis.getenv \"MY_VAR\"` with a literal name, or refactor so the name is known before mono runs.",
        ),
    ),
    (
        "UrpLibraryProjectParseFailed",
        _p(
            "The library project `{0}` listed in your `.urp` could not be merged.\n\nParser detail: {1}",
        ),
    ),
    (
        "UrpUnrecognizedDirective",
        _p(
            "`.urp` line starts with `{0}`, which Ur/Web does not recognize as a directive.\n\n"
            "Compare with the manual’s directive list (`library`, `database`, `sql`, …).",
        ),
    ),
    (
        "CompilerInternalLockPoisoned",
        _p(
            "The compiler hit an internal lock problem ({0}).\n\n"
            "That usually means an earlier pass panicked while holding the lock.\n"
            "Try a clean rebuild; if it keeps happening, please report a bug.",
            "Kompilatorn stötte på ett internt låsproblem ({0}).\n\n"
            "Det betyder ofta att ett tidigare pass panikerade medan det höll låset.\n"
            "Försök bygga om från ett rent tillstånd. Om det fortsätter, rapportera en bugg.",
            "El compilador encontró un problema interno de bloqueo ({0}).\n\n"
            "Suele significar que una fase anterior entró en pánico mientras mantenía el bloqueo.\n"
            "Intente reconstruir desde un estado limpio. Si persiste, notifique un error.",
        ),
    ),
    (
        "CoreEspecializeMissingSpecializationMetadata",
        _p(
            "Specialization metadata for `{0}` was missing when the core pass tried to rewrite a call.\n\n"
            "Fix earlier errors, or report a bug if elaboration reported success.",
        ),
    ),
    (
        "CoreLocalReductionStaticCaseArmMissing",
        _p(
            "While simplifying a `case`, no static arm matched even though the discriminant looked decided — span {0}.\n\n"
            "This is often a compiler limitation on very complex `case` shapes; try splitting the `case` or report a bug.",
        ),
    ),
]

for _name, _tri in _POST:
    add(_name, _tri[0], _tri[1], _tri[2])
