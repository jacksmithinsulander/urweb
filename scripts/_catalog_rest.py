# Executed by gen_diagnostic_catalog.py — remainder of diagnostic catalog.


def _t(en: str, sv: str | None = None, es: str | None = None) -> tuple[str, str, str]:
    return (en, sv or en, es or en)


ROWS: list[tuple[str, tuple[str, str, str]]] = [
    ("ElabKindMismatch", _t("Kind mismatch: {0}")),
    ("ElabUnboundKindVariableTemplate", _t("Unbound kind variable `{0}`")),
    (
        "ElabConstructorRecursionDepth",
        _t(
            "Elaboration: constructor recursion depth exceeded 500 (internal limit — simplify types or report a bug)"
        ),
    ),
    ("ElabConstructorAppNonArrow", _t("Constructor application to non-arrow kind")),
    ("ElabTupleProjectionOutOfBounds", _t("Tuple projection out of bounds: {0}")),
    ("ElabTupleProjectionNonTuple", _t("Tuple projection from non-tuple kind")),
    ("ElabUnboundTypeConstructor", _t("Unbound type constructor `{0}`")),
    ("ElabUnboundModuleFirst", _t("Unbound module `{0}`")),
    ("ElabModuleNonConstSignature", _t("Module `{0}` has non-const signature")),
    ("ElabSubModuleNonConstSignature", _t("Sub-module `{0}` has non-const signature")),
    ("ElabNotAStructure", _t("`{0}` is not a structure")),
    ("ElabUnboundModule", _t("Unbound module `{0}`")),
    ("ElabUnboundRelConstructor", _t("Unbound constructor Rel({0})")),
    ("ElabUnboundNamedConstructor", _t("Unbound named constructor {0}")),
    ("ElabApplicationNonArrowKind", _t("Application to non-arrow kind")),
    ("ElabKAppNonKFun", _t("KApp to non-KFun kind")),
    ("ElabTypeMismatch", _t("Type mismatch: {0}")),
    ("ElabConstructorExpectsArgument", _t("Constructor `{0}` expects an argument")),
    ("ElabConstructorDoesNotTakeArgument", _t("Constructor `{0}` does not take an argument")),
    ("ElabUnboundConstructor", _t("Unbound constructor `{0}`")),
    (
        "ElabExpressionRecursionDepth",
        _t(
            "Elaboration: expression recursion depth exceeded 200 (internal limit — simplify the expression or report a bug)"
        ),
    ),
    ("ElabApplicationNonFunction", _t("Application to non-function type")),
    ("ElabConstructorAppNonTcFun", _t("Constructor application to non-TCFun type")),
    ("ElabUnboundVariable", _t("Unbound variable `{0}`")),
    (
        "ElabImplicitArgIterationLimit",
        _t(
            "Elaboration: implicit argument insertion exceeded 50 iterations (possible infinite type expansion — report a bug if this persists)"
        ),
    ),
    ("ElabUnboundDatatype", _t("Unbound datatype `{0}`")),
    ("ElabUnboundSignature", _t("Unbound signature `{0}`")),
    ("ElabUnboundModuleForSignature", _t("Unbound module `{0}`")),
    ("ElabSignatureMismatch", _t("Signature mismatch")),
    ("ElabSignatureMissingValue", _t("Signature missing value `{0}`")),
    ("ElabKindMismatchForSignatureValue", _t("Kind mismatch for `{0}`: {1}")),
    ("ElabWrongConstructorKindFor", _t("Wrong constructor kind for `{0}`")),
    ("ElabSignatureMissingType", _t("Signature missing type `{0}`")),
    ("ElabWrongTypeForSignature", _t("Wrong type for `{0}`")),
    ("ElabSignatureMissingStructure", _t("Signature missing structure `{0}`")),
    (
        "ElabCannotOpenNonConstModule",
        _t("cannot open structure: signature is not a constant module"),
    ),
    ("ElabUnboundStructure", _t("Unbound structure `{0}`")),
    ("ElabNoStructureInModule", _t("No structure `{0}` in module")),
    ("ElabApplicationNonFunctorStructure", _t("Application of non-functor structure")),
    ("ElabUnresolvedDisjointness", _t("Unresolved disjointness constraint")),
    ("ElabUnresolvedTypeclass", _t("Unresolved typeclass constraint: {0}")),
    ("CouldNotReadBasisUrs", _t("I could not read the Basis signature file `{0}`.\n\n{1}")),
    ("CouldNotReadTopUrs", _t("I could not read the Top signature `{0}`.\n\n{1}")),
    ("CouldNotReadTopUr", _t("I could not read the Top implementation `{0}`.\n\n{1}")),
    ("CouldNotReadFfiUrs", _t("I could not read the FFI signature `{0}`.\n\n{1}")),
    ("CouldNotReadSourceUr", _t("I could not read the source file `{0}`.\n\n{1}")),
    ("CouldNotReadSignatureUrs", _t("I could not read the signature `{0}`.\n\n{1}")),
    (
        "ParserNotLinkedUr",
        _t(
            "The `.ur` parser is not available in this build.\n\nRebuild with URWEB_GEN_PARSER=1 so the generated LALRPOP tables are linked in."
        ),
    ),
    (
        "ParserNotLinkedUrs",
        _t(
            "The `.urs` parser is not available in this build.\n\nRebuild with URWEB_GEN_PARSER=1 so the generated LALRPOP tables are linked in."
        ),
    ),
    (
        "ParseUrSyntaxFailed",
        _t("I could not parse `{0}` into valid Ur/Web syntax.\n\nParser detail:\n{1}"),
    ),
    (
        "HintParseUrSyntax",
        _t(
            "Start from the location in the detail above. Common fixes: balance `(` `[` `{{` and string quotes; inside `<xml>...</xml>` every tag must close and `{{...}}` splices must nest cleanly; in `query` / SQL splices check braces; in `fn`/`fun` bodies check `=>`."
        ),
    ),
    (
        "ParseUrXmlHeuristicNote",
        _t(
            "(Your file uses `<xml` — this diagnostic is labeled XML because problems are often mismatched tags or splices.)"
        ),
    ),
    (
        "ParseUrsSyntaxFailed",
        _t("I could not parse `{0}` into valid signature syntax.\n\nParser detail:\n{1}"),
    ),
    (
        "HintParseUrsSyntax",
        _t(
            "`.urs` files list `val`, `type`, `datatype`, `structure`, etc. Quantified arrows often look like `[nm :: Type] -> ...` with explicit brackets. Match keywords to the manual and balance brackets."
        ),
    ),
    (
        "SqlCompatExprFragmentParseFailed",
        _t(
            "The legacy SQL compatibility rewrite could not re-parse an expression fragment.\n\nParser errors:\n{0}",
            "SQL-kompatibilitetsomskrivningen kunde inte tolka om ett uttrycksfragment.\n\nParsefel:\n{0}",
            "La reescritura de compatibilidad SQL no pudo volver a analizar un fragmento de expresión.\n\nErrores de análisis:\n{0}",
        ),
    ),
    (
        "SqlCompatExprFragmentPatternMismatch",
        _t(
            "The legacy SQL compatibility rewrite produced an unexpected pattern when wrapping an expression fragment.",
            "SQL-kompatibilitetsomskrivningen producerade ett oväntat mönster vid inbäddning av uttrycksfragment.",
            "La reescritura de compatibilidad SQL produjo un patrón inesperado al envolver un fragmento de expresión.",
        ),
    ),
    (
        "SqlCompatExprFragmentDeclMismatch",
        _t(
            "The legacy SQL compatibility rewrite produced an unexpected declaration when wrapping an expression fragment.",
            "SQL-kompatibilitetsomskrivningen producerade en oväntad deklaration vid inbäddning av uttrycksfragment.",
            "La reescritura de compatibilidad SQL produjo una declaración inesperada al envolver un fragmento de expresión.",
        ),
    ),
    (
        "SqlCompatConFragmentParseFailed",
        _t(
            "The legacy SQL compatibility rewrite could not re-parse a constructor fragment.\n\nParser errors:\n{0}",
            "SQL-kompatibilitetsomskrivningen kunde inte tolka om ett konstruktorfragment.\n\nParsefel:\n{0}",
            "La reescritura de compatibilidad SQL no pudo volver a analizar un fragmento de constructor.\n\nErrores de análisis:\n{0}",
        ),
    ),
    (
        "SqlCompatConFragmentDeclMismatch",
        _t(
            "The legacy SQL compatibility rewrite produced an unexpected declaration when wrapping a constructor fragment.",
            "SQL-kompatibilitetsomskrivningen producerade en oväntad deklaration vid inbäddning av konstruktorfragment.",
            "La reescritura de compatibilidad SQL produjo una declaración inesperada al envolver un fragmento de constructor.",
        ),
    ),
    (
        "SqlCompatDynamicFieldMissingBraces",
        _t(
            "Dynamic SQL field reference is missing its closing `}}`: {0}",
            "Dynamisk SQL-fältreferens saknar avslutande `}}`: {0}",
            "La referencia de campo SQL dinámico le falta el `}}` de cierre: {0}",
        ),
    ),
    (
        "SqlCompatFieldMissingBrace",
        _t(
            "SQL field reference is missing its closing `}}`: {0}",
            "SQL-fältreferens saknar avslutande `}}`: {0}",
            "La referencia de campo SQL le falta el `}}` de cierre: {0}",
        ),
    ),
    (
        "SqlCompatDynamicSelectFieldMissingBraces",
        _t(
            "Dynamic SELECT field is missing its closing `}}`: {0}",
            "Dynamiskt SELECT-fält saknar avslutande `}}`: {0}",
            "El campo SELECT dinámico le falta el `}}` de cierre: {0}",
        ),
    ),
    (
        "SqlCompatUnsupportedExpression",
        _t(
            "The legacy SQL compatibility rewrite does not support this expression form: {0}",
            "SQL-kompatibilitetsomskrivningen stöder inte denna uttrycksform: {0}",
            "La reescritura de compatibilidad SQL no soporta esta forma de expresión: {0}",
        ),
    ),
    (
        "SqlCompatUnsupportedSelectItem",
        _t(
            "The legacy SQL compatibility rewrite does not support this SELECT item: {0}",
            "SQL-kompatibilitetsomskrivningen stöder inte detta SELECT-element: {0}",
            "La reescritura de compatibilidad SQL no soporta este elemento SELECT: {0}",
        ),
    ),
    (
        "SqlCompatUnsupportedPlaceholder",
        _t(
            "The legacy SQL compatibility rewrite does not support this SQL placeholder payload: {0}",
            "SQL-kompatibilitetsomskrivningen stöder inte denna SQL-platshållarens innehåll: {0}",
            "La reescritura de compatibilidad SQL no soporta este contenido de marcador SQL: {0}",
        ),
    ),
    (
        "SqlCompatLeftJoinMissingOn",
        _t(
            "LEFT JOIN is missing its ON clause.",
            "LEFT JOIN saknar ON-sats.",
            "El LEFT JOIN no tiene cláusula ON.",
        ),
    ),
    (
        "SqlCompatJoinMissingOn",
        _t(
            "JOIN is missing its ON clause.",
            "JOIN saknar ON-sats.",
            "El JOIN no tiene cláusula ON.",
        ),
    ),
    (
        "SqlCompatSelectMissingFrom",
        _t(
            "SELECT is missing its FROM clause.",
            "SELECT saknar FROM-sats.",
            "El SELECT no tiene cláusula FROM.",
        ),
    ),
    (
        "SqlCompatInsertMissingInto",
        _t(
            "INSERT is missing its INTO clause.",
            "INSERT saknar INTO-sats.",
            "El INSERT no tiene cláusula INTO.",
        ),
    ),
    (
        "SqlCompatInsertMissingFieldList",
        _t(
            "INSERT is missing its field list.",
            "INSERT saknar fältlista.",
            "El INSERT no tiene lista de campos.",
        ),
    ),
    (
        "SqlCompatInsertFieldListMissingParen",
        _t(
            "INSERT field list is missing its closing parenthesis.",
            "INSERT-fältlistan saknar avslutande parentes.",
            "La lista de campos del INSERT le falta el paréntesis de cierre.",
        ),
    ),
    (
        "SqlCompatInsertMissingValues",
        _t(
            "INSERT is missing its VALUES clause.",
            "INSERT saknar VALUES-sats.",
            "El INSERT no tiene cláusula VALUES.",
        ),
    ),
    (
        "SqlCompatInsertValuesMissingOpenParen",
        _t(
            "INSERT values list is missing its opening parenthesis.",
            "INSERT-värdelistan saknar inledande parentes.",
            "La lista de valores del INSERT le falta el paréntesis de apertura.",
        ),
    ),
    (
        "SqlCompatInsertValuesMissingCloseParen",
        _t(
            "INSERT values list is missing its closing parenthesis.",
            "INSERT-värdelistan saknar avslutande parentes.",
            "La lista de valores del INSERT le falta el paréntesis de cierre.",
        ),
    ),
    (
        "SqlCompatDeleteMissingFrom",
        _t(
            "DELETE is missing its FROM clause.",
            "DELETE saknar FROM-sats.",
            "El DELETE no tiene cláusula FROM.",
        ),
    ),
    (
        "SqlCompatDeleteMissingWhere",
        _t(
            "DELETE is missing its WHERE clause.",
            "DELETE saknar WHERE-sats.",
            "El DELETE no tiene cláusula WHERE.",
        ),
    ),
    (
        "SqlCompatUpdateMissingSet",
        _t(
            "UPDATE is missing its SET clause.",
            "UPDATE saknar SET-sats.",
            "El UPDATE no tiene cláusula SET.",
        ),
    ),
    (
        "SqlCompatUpdateMissingWhere",
        _t(
            "UPDATE is missing its WHERE clause.",
            "UPDATE saknar WHERE-sats.",
            "El UPDATE no tiene cláusula WHERE.",
        ),
    ),
    (
        "SqlCompatUpdateAssignmentMissingEquals",
        _t(
            "UPDATE assignment is missing its `=` operator.",
            "UPDATE-tilldelning saknar `=`-operator.",
            "La asignación del UPDATE le falta el operador `=`.",
        ),
    ),
    (
        "ExplifyKindErrorPlaceholder",
        _t(
            "The elaborator marked this kind as invalid, but explify still saw it.",
            "Elaboratorn markerade denna sort som ogiltig, men explify såg den ändå.",
            "El elaborador marcó esta clase como inválida, pero explify aún la vio.",
        ),
    ),
    (
        "HintExplifyKindErrorPlaceholder",
        _t(
            "Fix the earlier kind or signature error that produced this placeholder.",
            "Åtgärda det tidigare sort- eller signaturfel som gav denna platshållare.",
            "Corrige antes el error de clase o firma que produjo este marcador.",
        ),
    ),
    (
        "ExplifyKindMetavarUnknown",
        _t(
            "Kind inference left a metavariable unknown while converting to the explicit AST.",
            "Sortinferens lämnade en metaplatshållare okänd vid konvertering till explicit AST.",
            "La inferencia de clases dejó un metavariable desconocido al convertir al AST explícito.",
        ),
    ),
    (
        "HintExplifyKindMetavarUnknown",
        _t(
            "Add kind annotations or rebuild; if elaboration succeeded, report a compiler bug.",
            "Lägg till sortannoteringar eller bygg om; om elaboration lyckades, rapportera en kompilatorbugg.",
            "Añade anotaciones de clase o recompila; si la elaboración tuvo éxito, reporta un fallo del compilador.",
        ),
    ),
    (
        "ExplifyTupleKindMetavarUnknown",
        _t(
            "Tuple kind inference did not finish before the explify pass.",
            "Tupelsortinferens blev inte klar före explify-passet.",
            "La inferencia de la clase de tupla no terminó antes del pase explify.",
        ),
    ),
    (
        "HintExplifyTupleKindMetavarUnknown",
        _t(
            "Annotate tuple kinds explicitly, or fix upstream kind errors first.",
            "Annotera tupelsorter explicit, eller åtgärda uppströms sortfel först.",
            "Anota las clases de tupla explícitamente o corrige primero errores de clase anteriores.",
        ),
    ),
    (
        "ExplifyUnexpectedConstructorError",
        _t("Explify: unexpected constructor error placeholder"),
    ),
    (
        "ExplifyConstructorMetavarUnknown",
        _t(
            "Type inference left a metavariable unknown while converting to the explicit AST.",
            "Typinferens lämnade en metaplatshållare okänd vid konvertering till explicit AST.",
            "La inferencia de tipos dejó un metavariable desconocido al convertir al AST explícito.",
        ),
    ),
    (
        "HintExplifyConstructorMetavarUnknown",
        _t(
            "This usually means elaboration should have failed earlier; add annotations or rebuild — if it persists, report a compiler bug.",
            "Detta betyder ofta att elaboration borde ha misslyckats tidigare; lägg till annoteringar eller bygg om — om det kvarstår, rapportera en bugg.",
            "Suele significar que la elaboración debió fallar antes; añade anotaciones o recompila — si persiste, reporta un fallo.",
        ),
    ),
    (
        "ExplifyUnexpectedExpressionError",
        _t("Explify: unexpected expression error placeholder"),
    ),
    ("ExplifyExpressionUnificationUnknown", _t("Explify: expression unification still unknown")),
    (
        "ExplifyTypedHoleRemains",
        _t("Explify: typed hole remains (fill the hole or fix the type error)"),
    ),
    (
        "ExplifyLocalValRecShouldBeLifted",
        _t("Explify: local `val rec` should have been lifted by unnest"),
    ),
    (
        "ExplifySignatureErrorPlaceholder",
        _t(
            "The elaborator marked this signature as invalid, but explify still saw it.",
            "Elaboratorn markerade denna signatur som ogiltig, men explify såg den ändå.",
            "El elaborador marcó esta firma como inválida, pero explify aún la vio.",
        ),
    ),
    (
        "HintExplifySignatureErrorPlaceholder",
        _t(
            "Fix earlier type or signature errors first; the surrounding interface may be inconsistent.",
            "Åtgärda tidigare typ- eller signaturfel först; det omgivande gränssnittet kan vara inkonsekvent.",
            "Corrige antes errores de tipo o firma; la interfaz circundante puede ser inconsistente.",
        ),
    ),
    (
        "ExplifyStructureErrorPlaceholder",
        _t(
            "The elaborator marked this structure as invalid, but explify still saw it.",
            "Elaboratorn markerade denna struktur som ogiltig, men explify såg den ändå.",
            "El elaborador marcó esta estructura como inválida, pero explify aún la vio.",
        ),
    ),
    (
        "HintExplifyStructureErrorPlaceholder",
        _t(
            "Resolve structure or functor errors in the source before this pass.",
            "Lös struktur- eller funktor-fel i källan före detta pass.",
            "Resuelve errores de estructura o functor en el código antes de este pase.",
        ),
    ),
    (
        "UnnestRemapFailedInternal",
        _t(
            "Internal: unnest remap failed (free-var index {0} missing from {1:?}) — report a bug"
        ),
    ),
    (
        "InformationFlowPolicyViolation",
        _t(
            "This expression may break the declared information-flow policy (data could flow where it should not).",
            "Detta uttryck kan bryta den deklarerade informationsflödespolicyn (data kan hamna fel).",
            "Esta expresión puede violar la regulación de flujo de información declarada.",
        ),
    ),
    (
        "HintInformationFlowPolicyViolation",
        _t(
            "Review `policy` rules and simplify the expression so trusted values are built only from allowed sources.",
            "Granska `policy`-regler och förenkla uttrycket så pålitliga värden bara byggs från tillåtna källor.",
            "Revisa las reglas `policy` y simplifica la expresión para que los valores de confianza provengan solo de fuentes permitidas.",
        ),
    ),
    (
        "DatabasePolicyMayViolate",
        _t("This {0} may violate the corresponding database policy."),
    ),
    (
        "HintDatabasePolicyMayViolate",
        _t(
            "Check matching `policy` declarations for insert/update/delete and tighten the proof obligations.",
            "Kontrollera matchande `policy`-deklarationer för insert/update/delete och skärp proof-skyldigheterna.",
            "Revisa las declaraciones `policy` de insert/update/delete y endurece las obligaciones de prueba.",
        ),
    ),
    (
        "SerializationExcludedTypes",
        _t(
            "Serialization is not allowed for this type: it contains excluded types ({0}).",
            "Serialisering är inte tillåten för denna typ: den innehåller utestängda typer ({0}).",
            "No se permite serializar este tipo: contiene tipos excluidos ({0}).",
        ),
    ),
    (
        "HintSerializationExcludedTypes",
        _t(
            "Narrow the marshalled type, or avoid serializing values that embed channels, pages, or other server-only constructors.",
            "Avgränsa den marschallerade typen, eller undvik att serialisera värden med kanaler, sidor eller andra endast-server-konstruktorer.",
            "Reduce el tipo empaquetado, o evita serializar valores con canales, páginas u otros constructores solo servidor.",
        ),
    ),
    (
        "ExportNamesUndefinedValue",
        _t("`export` names a value that is not defined in this module."),
    ),
    (
        "HintExportNamesUndefinedValue",
        _t(
            "Declare the value before the export, or fix the spelling of the exported name.",
            "Deklarera värdet fore exporten, eller rätta stavningen av exportnamnet.",
            "Declara el valor antes del export, o corrige el nombre exportado.",
        ),
    ),
    (
        "ExportedHandlerUnsafeTypes",
        _t(
            "The exported handler `{0}` exposes argument types that cannot cross the HTTP boundary: {1}."
        ),
    ),
    (
        "HintExportedHandlerUnsafeTypes",
        _t(
            "Use plain data in the handler interface (records, sums without signals, etc.).",
            "Använd enkla data i handlargränssnittet (poster, summor utan signaler, etc.).",
            "Usa datos simples en la interfaz del manejador (registros, sumas sin señales, etc.).",
        ),
    ),
    (
        "CookieStoresUnmarshallableTypes",
        _t("Cookie `{0}` stores types that cannot be marshalled safely: {1}."),
    ),
    (
        "HintCookieStoresUnmarshallableTypes",
        _t(
            "Cookies must hold simple serializable data; remove channels, pages, and similar types.",
            "Cookies måste hålla enkel serialiserbar data; ta bort kanaler, sidor och liknande typer.",
            "Las cookies deben contener datos serializables simples; elimina canales, páginas y tipos similares.",
        ),
    ),
    (
        "TerminationValRecNotProved",
        _t(
            "I cannot prove that these mutually recursive `val rec` functions terminate.",
            "Jag kan inte bevisa att dessa ömsesidigt rekursiva `val rec`-funktioner terminerar.",
            "No puedo demostrar que estas funciones `val rec` mutuamente recursivas terminan.",
        ),
    ),
    (
        "HintTerminationValRecNotProved",
        _t(
            "Add a structurally decreasing argument (e.g. peel constructors in each recursive call), or split the logic so recursion is clearly well-founded.",
            "Lägg till ett strukturellt minskande argument (t.ex. skala konstruktorer i varje rekursivt anrop), eller dela logiken så rekursion är välgrundad.",
            "Añade un argumento que decrezca estructuralmente (p. ej. desmonta constructores en cada llamada), o divide la lógica para que la recursión esté bien fundada.",
        ),
    ),
    (
        "RpcInternalMissingTranslation",
        _t(
            "Internal compiler error: rpc/tryRpc application is missing the translation expression.\nThis is unexpected — if you can reproduce it with a small program, please report a bug."
        ),
    ),
    (
        "RpcCodeNotNamedFunction",
        _t("RPC code doesn't use a named function or transaction"),
    ),
    ("RpcUndetectedTransactionFunction", _t("Rpcify: undetected transaction function")),
    ("ExportDuplicateUrlPrefix", _t("Duplicate URL prefix {0}")),
    (
        "ExportFunctionMultipleModes",
        _t("Function {0} needed for multiple modes (link, form, RPC handler)."),
    ),
    (
        "ExportFunctionMultipleModesShort",
        _t("Function {0} needed for multiple modes"),
    ),
    ("ExportInvalidTagExpression", _t("Invalid {0} expression")),
    (
        "IoSomethingWrongReadingWriting",
        _t(
            "Something went wrong reading or writing a file:",
            "Något gick fel vid läsning eller skrivning av en fil:",
            "Algo salió mal al leer o escribir un archivo:",
        ),
    ),
    (
        "LspUnusedValueNeverUsedFromEntry",
        _t("Value `{0}` is never used from an entry point of this program."),
    ),
    (
        "HintLspUnusedValueNeverUsedFromEntry",
        _t(
            "Delete it, export it, or reference it from a page, table, task, or another root declaration.",
            "Ta bort det, exportera det, eller referera från en sida, tabell, uppgift eller annan rotdeklaration.",
            "Bórralo, expórtalo o refiérencialo desde una página, tabla, tarea u otra declaración raíz.",
        ),
    ),
    (
        "LspUnusedValRecNotReachable",
        _t("Value `{0}` in this `val rec` group is not reachable from an entry point."),
    ),
    (
        "HintLspUnusedValRecNotReachable",
        _t(
            "Remove the binding, or wire it into something the compiler treats as live code.",
            "Ta bort bindningen, eller koppla den till något kompilatorn behandlar som levande kod.",
            "Elimina el enlace, o conéctalo a algo que el compilador trate como código vivo.",
        ),
    ),
    (
        "CjrizeAnonymousFunctionRemains",
        _t("Anonymous function remains at code generation"),
    ),
    ("CjrizeNestedClosureRemains", _t("Nested closure remains in code generation")),
    (
        "CjrizeJavaScriptStillPresent",
        _t(
            "Embedded JavaScript is still present where the C backend expects it to be eliminated."
        ),
    ),
    (
        "HintCjrizeJavaScriptStillPresent",
        _t(
            "Move this fragment to client-only code, or ensure the mono pipeline removes `JavaScript` nodes before cjrize.",
        ),
    ),
    (
        "CjrizeSignalReturnInvalidServer",
        _t("Signal `return` is not valid in server-side lowered code."),
    ),
    (
        "HintCjrizeSignalReturnInvalidServer",
        _t("Restructure so signals are compiled only on the client path, or avoid signal operations in this transaction."),
    ),
    (
        "CjrizeSignalBindInvalidServer",
        _t("Signal `bind` is not valid in server-side lowered code."),
    ),
    (
        "HintCjrizeSignalBindInvalidServer",
        _t("Keep signal plumbing in client code; the server pass cannot emit bind for signals here."),
    ),
    (
        "CjrizeSignalSourceInvalidServer",
        _t("Signal `source` is not valid in server-side lowered code."),
    ),
    (
        "HintCjrizeSignalSourceInvalidServer",
        _t("Declare sources on the client surface, not inside server-only computations."),
    ),
    (
        "CjrizeRpcStillOnServer",
        _t("An RPC/server call is still present in code meant to run only on the server."),
    ),
    (
        "HintCjrizeRpcStillOnServer",
        _t("Split client vs server actions so RPCs are emitted on the browser side."),
    ),
    (
        "CjrizeChannelRecvUnsupportedServer",
        _t("Channel receive is not supported in this server-side fragment."),
    ),
    (
        "HintCjrizeChannelRecvUnsupportedServer",
        _t(
            "Use messaging patterns the mono pass can compile, or move receives to allowed contexts."
        ),
    ),
    ("CjrizeSleepInvalidServer", _t("`sleep` cannot appear in this server-side fragment.")),
    (
        "HintCjrizeSleepInvalidServer",
        _t("Delay or schedule work with constructs the backend supports."),
    ),
    (
        "CjrizeSpawnInvalidServer",
        _t("Thread spawn cannot appear in this server-side fragment."),
    ),
    (
        "HintCjrizeSpawnInvalidServer",
        _t("Avoid spawning OS threads in transactional server code."),
    ),
    (
        "CjrizeTableConstraintNotSimpleString",
        _t(
            "This table constraint is not a simple string field yet, so I cannot flatten it to SQL."
        ),
    ),
    (
        "HintCjrizeTableConstraintNotSimpleString",
        _t(
            "Use literal string values in constraint records after the mono passes have simplified them."
        ),
    ),
    (
        "MutationTestingBadPlaceholder",
        _t("bad"),
    ),
]

CORIFY = [
    (
        "CorifyInternalCannotDeclareTypeInFfi",
        "Corify: internal error — cannot declare a type name inside FFI flattening",
    ),
    (
        "CorifyInternalCannotBindValueInFfi",
        "Corify: internal error — cannot bind a value inside FFI flattening",
    ),
    (
        "CorifyInternalCannotBindDataConstructorValueInFfi",
        "Corify: internal error — cannot bind a data constructor value inside FFI flattening",
    ),
    (
        "CorifyInternalCannotBindDataConstructorInFfi",
        "Corify: internal error — cannot bind a data constructor inside FFI flattening",
    ),
    (
        "CorifyStructureNestingStackUnderflow",
        "Corify: structure nesting stack underflow (compiler internal state)",
    ),
    (
        "CorifyInternalCannotBindNestedStructureInFfi",
        "Corify: internal error — cannot bind a nested structure inside FFI flattening",
    ),
    (
        "CorifyInternalCannotBindFunctorInFfi",
        "Corify: internal error — cannot bind a functor inside FFI flattening",
    ),
    ("CorifyUnknownStructureIdInPath", "Corify: unknown structure id {0} in module path"),
    ("CorifyUnknownSubmoduleInPath", "Corify: unknown submodule `{0}` in module path"),
    (
        "CorifyNotValueOrConstructorAtPath",
        "Corify: `{0}` is not a value or data constructor at this module path",
    ),
    (
        "CorifyUnknownImportedDataConstructor",
        "Corify: unknown imported data constructor `{0}`",
    ),
    (
        "CorifyInternalValBindingExpectedNamed",
        "Corify: internal error — val binding expected to be Named here",
    ),
    (
        "CorifyNotSubmoduleOrFunctor",
        "Corify: `{0}` is not a submodule or functor visible in this structure",
    ),
    ("CorifyUnknownStructureVariableId", "Corify: unknown structure variable id {0}"),
    ("CorifyNonConstFfiSignature", "Non-const signature for FFI structure"),
    ("CorifyStructureTooFancyToExport", "Structure is too fancy to export"),
    (
        "CorifyBasisMissingForExport",
        "Corify: Basis FFI module is missing; cannot compile 'export' of a page",
    ),
    (
        "CorifyExportDidNotCorifyToGlobalName",
        "Corify: exported value did not corify to a global name (skipping with a placeholder id)",
    ),
    ("CorifyNonConstSignatureForExport", "Non-const signature for 'export'"),
    ("CorifyWrongOnErrorIdentifier", "Wrong type of identifier for 'onError'"),
    (
        "CorifyFfiNotAtModuleTopLevel",
        "Used 'ffi' declaration beneath module top level",
    ),
    ("CorifyUnknownStructureId", "Corify: unknown structure id {0}"),
    (
        "CorifyUnknownSubmoduleInProjection",
        "Corify: unknown submodule `{0}` in structure projection",
    ),
    (
        "CorifyNestedFunctorInApplicationUnsupported",
        "Corify: nested functor definitions inside functor applications are not supported",
    ),
    (
        "CorifyFunctorApplicationUnsupportedForm",
        "Corify: functor application is not in a supported form (expected path to a functor)",
    ),
]

MONO_OPT_INVALID = [
    ("InvalidHtml5DataAttribute", "Invalid HTML5 data-* attribute {0}"),
    ("InvalidUrlPassedToBless", "Invalid URL {0} passed to 'bless'"),
    ("InvalidStringPassedToBlessMime", "Invalid string {0} passed to 'blessMime'"),
    ("InvalidStringPassedToAtom", "Invalid string {0} passed to 'atom'"),
    ("InvalidUrlPassedToCssUrl", "Invalid URL {0} passed to 'css_url'"),
    ("InvalidStringPassedToProperty", "Invalid string {0} passed to 'property'"),
    (
        "InvalidStringPassedToBlessRequestHeader",
        "Invalid string {0} passed to 'blessRequestHeader'",
    ),
    (
        "InvalidStringPassedToBlessResponseHeader",
        "Invalid string {0} passed to 'blessResponseHeader'",
    ),
    ("InvalidStringPassedToBlessEnvVar", "Invalid string {0} passed to 'blessEnvVar'"),
    ("InvalidStringPassedToBlessMeta", "Invalid string {0} passed to 'blessMeta'"),
]

for _name, _tup in ROWS:
    add(_name, _tup[0], _tup[1], _tup[2])

for _name, _en in CORIFY:
    add(_name, _en, _en, _en)

for _name, _en in MONO_OPT_INVALID:
    add(_name, _en, _en, _en)

_PATH_SCRIPT_SIDE_SQL = [
    (
        "PathTwoConstraintsSameGeneratedPath",
        "Two constraints want the same generated path `{0}` for this table.",
        "Två villkor vill ha samma genererade sökväg `{0}` för denna tabell.",
        "Dos restricciones quieren la misma ruta generada `{0}` para esta tabla.",
    ),
    (
        "HintPathTwoConstraintsSameGeneratedPath",
        "Rename one constraint or split the table so SQL constraint names stay unique.",
        "Byt namn på ett villkor eller dela tabellen så SQL-villkorsnamn förblir unika.",
        "Renombra una restricción o divide la tabla para que los nombres SQL sigan siendo únicos.",
    ),
    (
        "PathTwoExportsSameUrl",
        "Two pages or actions export the same URL path `{0}`.",
        "Två sidor eller åtgärder exporterar samma URL-sökväg `{0}`.",
        "Dos páginas o acciones exportan la misma ruta URL `{0}`.",
    ),
    (
        "HintPathTwoExportsSameUrl",
        "Give each `export` a distinct path string, or merge the handlers.",
        "Ge varje `export` en unik sökvägssträng, eller slå ihop hanterarna.",
        "Dale a cada `export` una ruta distinta, o fusiona los manejadores.",
    ),
    (
        "PathTableOrSequenceDeclaredTwice",
        "A table or sequence named `{0}` is declared twice.",
        "En tabell eller sekvens med namnet `{0}` är deklarerad två gånger.",
        "Una tabla o secuencia `{0}` está declarada dos veces.",
    ),
    (
        "HintPathTableOrSequenceDeclaredTwice",
        "Rename one declaration, or drop the duplicate.",
        "Byt namn på en deklaration, eller ta bort dubbletten.",
        "Renombra una declaración o elimina el duplicado.",
    ),
    (
        "PathPrimaryKeyMetadataCollides",
        "Primary key metadata for `{0}` collides with another path.",
        "Primärnyckelmetadata för `{0}` kolliderar med en annan sökväg.",
        "Los metadatos de clave primaria para `{0}` chocan con otra ruta.",
    ),
    (
        "HintPathPrimaryKeyMetadataCollides",
        "Adjust the table name or constraints so generated paths stay unique.",
        "Justera tabellnamn eller villkor så genererade sökvägar förblir unika.",
        "Ajusta el nombre de tabla o restricciones para que las rutas sigan siendo únicas.",
    ),
    (
        "PathTwoCookiesSharePath",
        "Two cookies share the internal path `{0}`.",
        "Två cookies delar den interna sökvägen `{0}`.",
        "Dos cookies comparten la ruta interna `{0}`.",
    ),
    (
        "HintPathTwoCookiesSharePath",
        "Use different cookie names so the runtime can tell them apart.",
        "Använd olika cookienamn så körningen kan skilja dem åt.",
        "Usa nombres de cookie distintos para que el runtime los distinga.",
    ),
    (
        "PathTwoStylesSamePath",
        "Two `style` declarations use the same path `{0}`.",
        "Två `style`-deklarationer använder samma sökväg `{0}`.",
        "Dos declaraciones `style` usan la misma ruta `{0}`.",
    ),
    (
        "HintPathTwoStylesSamePath",
        "Assign each stylesheet a unique path.",
        "Ge varje stilmall en unik sökväg.",
        "Asigna a cada hoja de estilos una ruta única.",
    ),
    (
        "ScriptPushProtocolNotPersistent",
        "This program uses server push, but the chosen protocol `{0}` does not support it.",
        "Programmet använder server-push, men valt protokoll `{0}` stöder det inte.",
        "Este programa usa server push, pero el protocolo `{0}` no lo admite.",
    ),
    (
        "HintScriptPushProtocolNotPersistent",
        "Switch to a Web-capable protocol in project settings, or remove features that require push.",
        "Byt till ett webbkapabelt protokoll i projektinställningar, eller ta bort funktioner som kräver push.",
        "Cambia a un protocolo adecuado para la web en ajustes del proyecto, o elimina funciones que requieran push.",
    ),
    (
        "SideServerCallsClientOnlyFfi",
        "Server code calls `{0}.{1}`, which is only allowed on the client.",
        "Serverkod anrokar `{0}.{1}`, vilket bara är tillåtet på klienten.",
        "El código servidor llama `{0}.{1}`, que solo está permitido en el cliente.",
    ),
    (
        "HintSideServerCallsClientOnlyFfi",
        "Move this call into `<script>` / client code, or use a server-safe alternative.",
        "Flytta anropet till `<script>`/klientkod, eller använd ett serversäkert alternativ.",
        "Mueve esta llamada a `<script>` / código cliente, o usa una alternativa segura en servidor.",
    ),
    (
        "SqlTablePrimaryKeyNotKnownString",
        "The primary key expression for this `table` is not a known string yet — the compiler needs a fixed column name (or empty string) for DDL.",
        "Primärnyckeluttrycket för denna `table` är ännu inte en känd sträng — kompilatorn behöver ett fast kolumnnamn (eller tom sträng) för DDL.",
        "La expresión de clave primaria de esta `table` aún no es una cadena fija; el compilador necesita un nombre de columna (o cadena vacía) para el DDL.",
    ),
    (
        "HintSqlTablePrimaryKeyNotKnownString",
        "Use a literal string for the PK field list, or simplify the expression so mono can fold it before code generation.",
        "Använd en literalfältlista för PK, eller förenkla uttrycket så mono kan vika det före kodgenerering.",
        "Usa una lista literal de campos para la PK, o simplifica la expresión para que mono la reduzca antes de generar código.",
    ),
    (
        "SqlViewNotPlainString",
        "This `view` does not yet reduce to a plain SQL string the backend can emit.",
        "Denna `view` har ännu inte reducerats till en vanlig SQL-sträng som backend kan skriva.",
        "Esta `view` aún no se reduce a una cadena SQL que el backend pueda emitir.",
    ),
    (
        "HintSqlViewNotPlainStringStrcat",
        "Build the view SQL with `Basis.strcat` / `sqlify*` on known values so the mono pass can turn it into one string literal.",
        "Bygg vy-SQL med `Basis.strcat` / `sqlify*` på kända värden så mono-passet kan göra en strängliteral.",
        "Construye el SQL de la vista con `Basis.strcat` / `sqlify*` sobre valores conocidos para que mono lo convierta en una literal.",
    ),
    (
        "HintSqlViewNotPlainStringLiteral",
        "Pass a literal SQL string, or use `Basis.viewify` on a fully-known `string`, after mono has simplified it.",
        "Skicka en liter SQL-sträng, eller använd `Basis.viewify` på en fullt känd `string` efter att mono förenklat.",
        "Pasa un literal SQL, o usa `Basis.viewify` sobre un `string` totalmente conocido tras simplificar mono.",
    ),
    (
        "CjrizeFunctionNotExplicitAtCodegen",
        "Function isn't explicit at code generation",
        "Funktionen är inte explicit vid kodgenerering",
        "La función no es explícita en la generación de código",
    ),
    (
        "CjrizeTaskKindNotFullyDetermined",
        "Task kind not fully determined",
        "Task-typen inte fullt bestämd",
        "El tipo de tarea no está totalmente determinado",
    ),
    (
        "CjrizeInitializerNotFullyDetermined",
        "Initializer has not been fully determined",
        "Initieraren har inte fullt bestämts",
        "El inicializador no está totalmente determinado",
    ),
]

for _row in _PATH_SCRIPT_SIDE_SQL:
    add(_row[0], _row[1], _row[2], _row[3])
