#!/usr/bin/env python3
"""Generate src/diagnostics/ids.rs and src/diagnostics/template_tables.rs from catalog data."""
from __future__ import annotations

import textwrap
from pathlib import Path


def rust_string_literal(source_text: str) -> str:
    """Escape `source_text` as a Rust `"..."` literal (no raw strings)."""
    escaped = (
        source_text.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\r", "\\r")
        .replace("\n", "\\n")
    )
    return f'"{escaped}"'

# (RustVariantName, en, sv, es) — use {0} {1} for placeholders
CATALOG: list[tuple[str, str, str, str]] = []

def add(name: str, en: str, sv: str, es: str) -> None:
    CATALOG.append((name, en, sv, es))

# Sentinel empty diagnostic body (mutation tests, defaults).
add("EmptyPlain", "", "", "")

# --- Elaboration errors (elaboration_errors.rs) ---
add("UnboundKindVariable", "I do not know what kind `{0}` stands for at this spot.", "Jag vet inte vilken sort `{0}` betyder här.", "No sé qué clase representa `{0}` en este lugar.")
add("HintUnboundKindVariable", "If this should be a parameter, declare it to the left of `::` or `:::` on the same binding.", "Om det ska vara en parameter, deklarera den till vänster om `::` eller `:::` i samma bindning.", "Si debe ser un parámetro, decláralo a la izquierda de `::` o `:::` en el mismo enlace.")

add("WildcardDisallowedInSignature", "A signature cannot use `_` (a wildcard) here.", "En signatur kan inte använda `_` (jokertecken) här.", "Una firma no puede usar `_` (comodín) aquí.")
add("HintWildcardDisallowedInSignature", "Write an explicit kind so other modules see what you promise.", "Skriv en explicit sort så andra moduler ser vad du lovar.", "Escribe una clase explícita para que otros módulos vean lo que prometes.")

add("UnboundConstructorVariable", "I do not have a type or constructor variable named `{0}` in scope.", "Jag har ingen typ- eller konstruktorvariabel `{0}` i omfånget.", "No tengo una variable de tipo o constructor `{0}` en el ámbito.")
add("HintUnboundConstructorVariable", "Check that the name is in scope, or add the missing type parameter to the declaration.", "Kontrollera att namnet finns i omfånget, eller lägg till den saknade typparametern i deklarationen.", "Comprueba que el nombre esté en ámbito o añade el parámetro de tipo que falta a la declaración.")

add("UnboundDatatypeName", "I cannot find a datatype named `{0}` to use in this type.", "Jag hittar ingen datatyp `{0}` att använda här i typen.", "No encuentro un tipo de datos `{0}` para usar en este tipo.")
add("HintUnboundDatatypeName", "Spell it like its `datatype` declaration, or `open` the module that defines it.", "Stava som i `datatype`-deklarationen, eller `open` modulen som definierar den.", "Escríbelo como en la declaración `datatype`, o `open` el módulo que lo define.")

add("UnboundStructureReference", "I cannot find a structure named `{0}` in this path.", "Jag hittar ingen struktur `{0}` i denna sökväg.", "No encuentro una estructura `{0}` en esta ruta.")
add("HintUnboundStructureReference", "Use `structure S = ...` / `structure S : Sig = ...`, or qualify with the correct module path.", "Använd `structure S = ...` / `structure S : Sig = ...`, eller kvalificera med rätt modulsökväg.", "Usa `structure S = ...` / `structure S : Sig = ...`, o califica con la ruta de módulo correcta.")

add("ConstructorWrongKind", "This type lives at the wrong kind (sort of type-of-types).\n\nHave {0}, need {1}; {2}", "Denna typ har fel sort (slags typtyper).\n\nHar {0}, behöver {1}; {2}", "Este tipo está en una clase incorrecta (especie de tipo de tipos).\n\nHay {0}, se necesita {1}; {2}")
add("HintConstructorWrongKind", "If you just started with Ur/Web: kinds sit to the left of `::` (`Type`, `Type -> Type`, …). Make sure type parameters and `con` declarations use the kind the signature promises.", "Om du precis börjat med Ur/Web: sorter står till vänster om `::` (`Type`, `Type -> Type`, …). Se till att typparametrar och `con`-deklarationer använder den sort som signaturen lovar.", "Si acabas de empezar con Ur/Web: las clases van a la izquierda de `::` (`Type`, `Type -> Type`, …). Asegúrate de que los parámetros de tipo y las declaraciones `con` usen la clase que la firma promete.")

add("DuplicateRecordFieldName", "The record field `{0}` appears more than once here.", "Postfältet `{0}` förekommer mer än en gång här.", "El campo de registro `{0}` aparece más de una vez aquí.")
add("HintDuplicateRecordFieldName", "Each label in a record type or value must be unique; remove or rename the extra one.", "Varje etikett i en posttyp eller ett postvärde måste vara unikt; ta bort eller byt namn på det extra.", "Cada etiqueta en un tipo o valor de registro debe ser única; elimina o renombra el duplicado.")

add("ProjectionIndexOutOfBounds", "This projection uses index {0}, but the tuple is not large enough.", "Projektionen använder index {0}, men tupeln är inte tillräckligt stor.", "Esta proyección usa el índice {0}, pero la tupla no es lo bastante grande.")
add("HintProjectionIndexOutOfBounds", "Count the components from the left (starting at #1 in source, internally 0-based) and use a valid index.", "Räkna komponenterna från vänster (börjar med #1 i källan, internt 0-baserat) och använd ett giltigt index.", "Cuenta los componentes desde la izquierda (empezando en #1 en el código, internamente base 0) y usa un índice válido.")

add("ProjectionKindMismatch", "I expected a tuple-like type to project from, but found kind {0}.", "Jag förväntade mig en tupellik typ att projicera från, men hittade sort {0}.", "Esperaba un tipo tipo tupla del que proyectar, pero la clase es {0}.")
add("HintProjectionKindMismatch", "Projection `#n` / field access only works on tuple or record shapes at this level.", "Projektion `#n` / fältåtkomst fungerar bara på tupel- eller postformer på denna nivå.", "La proyección `#n` / acceso a campo solo funciona sobre formas de tupla o registro en este nivel.")

add("ConstructorWildcardDisallowedInSignatureConstructor", "A signature cannot use `_` (a wildcard) in this constructor position.", "En signatur kan inte använda `_` (jokertecken) i denna konstruktorposition.", "Una firma no puede usar `_` (comodín) en esta posición de constructor.")
add("HintConstructorWildcardDisallowedInSignatureConstructor", "Name the type or copy it from an interface you are implementing.", "Namnge typen eller kopiera den från ett gränssnitt du implementerar.", "Nombra el tipo o cópialo de la interfaz que implementas.")

# Kind unification (embedded as {2} in other messages)
add("KindOccursCheckFailed", "Kind occurs check failed: {0} vs {1}", "Sort forekomstcheck misslyckades: {0} mot {1}", "Fallo de verificación de ocurrencia de clase: {0} frente a {1}")
add("IncompatibleKinds", "Incompatible kinds: {0} vs {1}", "Inkompatibla sorter: {0} mot {1}", "Clases incompatibles: {0} frente a {1}")
add("ScopePreventsKindUnification", "Scoping prevents kind unification: {0} vs {1}", "Omfång hindrar sorters unifiering: {0} mot {1}", "El ámbito impide unificar clases: {0} frente a {1}")

# Constructor unification
add("NestedKindUnificationFailure", "Kind unification failure: have {0}, need {1}; {2}", "Unifiering av sort misslyckades: har {0}, behöver {1}; {2}", "Fallo al unificar clases: hay {0}, se necesita {1}; {2}")
add("ConstructorOccursCheckFailed", "Constructor occurs check failed: {0} vs {1}", "Konstruktor-occurs-check misslyckades: {0} mot {1}", "Fallo de occurs-check del constructor: {0} frente a {1}")
add("IncompatibleConstructorsUnif", "Incompatible constructors: {0} vs {1}", "Inkompatibla konstruktorer: {0} mot {1}", "Constructores incompatibles: {0} frente a {1}")
add("TypeFunctionExplicitnessMismatch", "Differing constructor function explicitness: {0} vs {1}", "Skiljande explicithet för konstruktorfunktion: {0} mot {1}", "Explicitud distinta en la función constructora: {0} frente a {1}")
add("UnexpectedKindForKindofQuery", "Unexpected kind for kindof calculation (expecting {0}): kind {1}, con {2}", "Oväntad sort för kindof-beräkning (förväntade {0}): sort {1}, kon {2}", "Clase inesperada para cálculo kindof (se esperaba {0}): clase {1}, con {2}")
add("RecordConstructorUnificationFailure", "Cannot unify record constructors: {0} vs {1}{2}", "Kan inte unifiera postkonstruktorer: {0} mot {1}{2}", "No se pueden unificar constructores de registro: {0} frente a {1}{2}")
add("SuspendedLiftingClash", "Cannot unify two unification variables that both have suspended liftings; first: {0}; other: {1}", "Kan inte unifiera två unifieringsvariabler som båda har suspenderade lyftningar; först: {0}; annan: {1}", "No se pueden unificar dos variables de unificación con elevaciones suspendidas; primero: {0}; otra: {1}")
add("SubstitutionBlockedByDeepUnification", "Substitution in constructor is blocked by a too-deep unification variable; body: {1}", "Substitution i konstruktor blockeras av en för djup unifieringsvariabel; kropp: {1}", "La sustitución en el constructor está bloqueada por una variable de unificación demasiado profunda; cuerpo: {1}")
add("UnificationLiftingTooDeep", "Cannot reverse-engineer unification variable lifting", "Kan inte återkonstruera lyftning av unifieringsvariabel", "No se puede reconstruir la elevación de la variable de unificación")
add("ScopePreventsConstructorUnification", "Scoping prevents constructor unification: {0} vs {1}", "Omfång hindrar konstruktorunifiering: {0} mot {1}", "El ámbito impide unificar constructores: {0} frente a {1}")

# Expression errors
add("UnboundExpressionVariable", "I cannot find a value or local variable named `{0}` in scope.", "Jag hittar inget värde eller lokal variabel `{0}` i omfånget.", "No encuentro un valor o variable local `{0}` en el ámbito.")
add("HintUnboundExpressionVariable", "Check the spelling, or use `open` / a qualified name like `ModuleName.binding`.", "Kontrollera stavningen, eller använd `open` / ett kvalificerat namn som `ModuleName.binding`.", "Revisa la ortografía, o usa `open` / un nombre calificado como `ModuleName.binding`.")

add("UnboundStructureInExpression", "I cannot find a structure named `{0}` to use in this expression.", "Jag hittar ingen struktur `{0}` att använda i detta uttryck.", "No encuentro una estructura `{0}` para usar en esta expresión.")
add("HintUnboundStructureInExpression", "Declare it, `open` the right module, or fix the module path prefix.", "Deklarera den, `open` rätt modul, eller rätta modulprefixet.", "Declárala, haz `open` del módulo correcto o corrige el prefijo de módulo.")

add("ExpressionUnificationFailure", "This expression does not have the type I need here.\n\nTechnical detail — inferred {0}, expected {1}; {2}", "Detta uttryck har inte den typ jag behöver här.\n\nTeknisk detalj — infererad {0}, förväntad {1}; {2}", "Esta expresión no tiene el tipo que necesito aquí.\n\nDetalle técnico — inferido {0}, esperado {1}; {2}")
add("HintExpressionUnificationFailure", "Compare what you wrote with what this position expects (function vs value, tuple shape, record fields). A small type annotation on a `val` or `fn` often makes the fix obvious.", "Jämför det du skrev med vad denna position förväntar sig (funktion kontra värde, tupelform, postfält). En liten typannotering på `val` eller `fn` gör ofta lösningen tydlig.", "Compara lo que escribiste con lo que esta posición espera (función frente a valor, forma de tupla, campos del registro). Una anotación de tipo pequeña en `val` o `fn` suele aclarar la corrección.")

add("UnificationVariableObstructsOperation", "Type inference is still stuck on a placeholder, so I cannot `{0}` yet.", "Typinferens sitter fast på en platshållare, så jag kan inte `{0}` ännu.", "La inferencia de tipos sigue atascada en un marcador de posición, así que aún no puedo `{0}`.")

add("HintUnificationVariableObstructs", "Add a type annotation nearby (or break the expression into a named `val`) so the solver can finish before this check runs.", "Lägg till en typannotering i närheten (eller dela upp uttrycket i en namngiven `val`) så att lösaren kan bli klar innan denna kontroll körs.", "Añade una anotación de tipo cerca (o divide la expresión en un `val` con nombre) para que el resolvedor termine antes de esta comprobación.")

add("ExpressionWrongForm", "I need a {0} here, but this expression has a different shape.", "Jag behöver en {0} här, men detta uttryck har en annan form.", "Necesito un {0} aquí, pero esta expresión tiene otra forma.")
add("HintExpressionWrongForm", "Re-read the grammar for this position — for example use `fn ... => ...` where a function is required.", "Läs om grammatiken för denna position — till exempel använd `fn ... => ...` där en funktion krävs.", "Relee la gramática de esta posición — por ejemplo usa `fn ... => ...` donde haga falta una función.")

add("IncompatibleConstructorsExpression", "These two type shapes cannot be used together: {0} vs {1}.", "Dessa två tyFormer kan inte användas tillsammans: {0} mot {1}.", "Estas dos formas de tipo no pueden usarse juntas: {0} frente a {1}.")
add("HintIncompatibleConstructorsExpression", "Often this is a wrong `case` branch, mixing datatypes, or a bad record/tuple — line up the constructors carefully.", "Ofta är detta en fel `case`-gren, blandade datatyper, eller en dålig post/tupel — rikta in konstruktorerna noggrant.", "A menudo es una rama `case` equivocada, mezclar tipos de datos o un registro/tupla incorrecto — alinea los constructores con cuidado.")

add("DuplicatePatternVariable", "The name `{0}` is bound twice in the same pattern.", "Namnet `{0}` binds två gånger i samma mönster.", "El nombre `{0}` está ligado dos veces en el mismo patrón.")
add("HintDuplicatePatternVariable", "Rename one binding, or use `_` when you do not need the value.", "Byt namn på en bindning, eller använd `_` när du inte behöver värdet.", "Renombra un enlace, o usa `_` si no necesitas el valor.")

add("PatternUnificationFailure", "This pattern does not match the type flowing into the `case` / binding.\n\nTechnical detail — inferred {0}, expected {1}; {2}", "Mönstret passar inte typen som flödar in i `case` / bindningen.\n\nTeknisk detalj — infererad {0}, förväntad {1}; {2}", "El patrón no coincide con el tipo que entra en `case` / enlace.\n\nDetalle técnico — inferido {0}, esperado {1}; {2}")
add("HintPatternUnificationFailure", "Check the constructor name, nested patterns, and record labels against the datatype you are matching.", "Kontrollera konstruktorns namn, nästlade mönster och postetiketter mot den datatyp du matchar.", "Revisa el nombre del constructor, patrones anidados y etiquetas del registro frente al tipo de datos que casas.")

add("UnboundQualifiedConstructor", "I cannot find the constructor `{0}` for this pattern.", "Jag hittar inte konstruktorn `{0}` för detta mönster.", "No encuentro el constructor `{0}` para este patrón.")
add("HintUnboundQualifiedConstructor", "Make sure the datatype is in scope and the constructor name matches its definition.", "Se till att datatypen finns i omfånget och att konstruktorns namn stämmer med definitionen.", "Asegúrate de que el tipo de datos esté en ámbito y el constructor coincida con su definición.")

add("PatternConstructorGivenArgumentButExpectsNone", "This constructor does not take an argument, but the pattern supplies one.", "Denna konstruktor tar inget argument, men mönstret ger ett.", "Este constructor no toma argumento, pero el patrón proporciona uno.")
add("HintPatternConstructorGivenArgumentButExpectsNone", "Write the constructor alone (no parentheses), unless you truly have a unit-shaped value.", "Skriv konstruktorn ensam (inga parenteser), om du inte verkligen har ett enhetsvärde.", "Escribe el constructor solo (sin paréntesis), salvo que tengas realmente un valor unidad.")

add("PatternConstructorExpectsArgumentButNoneGiven", "This constructor needs a nested pattern, but none is written after its name.", "Denna konstruktor behöver ett nästlat mönster, men inget skrivs efter namnet.", "Este constructor necesita un patrón anidado, pero no hay ninguno tras su nombre.")
add("HintPatternConstructorExpectsArgumentButNoneGiven", "Add parentheses with the inner pattern, e.g. `Ctor (inner, ...)`.", "Lägg till parenteser med det inre mönstret, t.ex. `Ctor (inner, ...)`.", "Añade paréntesis con el patrón interior, p. ej. `Ctor (inner, ...)`.")

add("InexhaustiveCaseAnalysis", "Inexhaustive 'case'; missed case: {0}", "Ofullständigt `case`; saknat fall: {0}", "`case` no exhaustivo; falta el caso: {0}")

add("DuplicatePatternRecordField", "The record pattern binds `{0}` more than once.", "Postmönstret binder `{0}` mer än en gång.", "El patrón de registro liga `{0}` más de una vez.")
add("HintDuplicatePatternRecordField", "Keep a single binding per label, or use `_` for fields you ignore.", "Behåll en bindning per etikett, eller använd `_` för fält du ignorerar.", "Mantén un solo enlace por etiqueta, o usa `_` en campos que ignores.")

add("UnresolvableTypeClassInstance", "Cannot resolve type class instance; class constraint: {0}", "Kan inte lösa typklassinstans; klassvillkor: {0}", "No se puede resolver la instancia de clase de tipos; restricción: {0}")

add("TypeClassWildcardOutOfContext", "Type class wildcard occurs out of context{0}", "Typjokertecken förekommer utanför sammanhang{0}", "Comodín de clase de tipos fuera de contexto{0}")

add("IllegalRecursiveValueBinding", "`val rec {0}` must bind to a function written with `fn` / λ on the right-hand side.", "`val rec {0}` måste binda till en funktion skriven med `fn` / λ på höger sida.", "`val rec {0}` debe enlazar a una función escrita con `fn` / λ en el lado derecho.")
add("HintIllegalRecursiveValueBinding", "Write `val rec f = fn x => ...` so recursion goes through a delayed function body.", "Skriv `val rec f = fn x => ...` så rekursion går genom en fördröjd funktionskropp.", "Escribe `val rec f = fn x => ...` para que la recursión pase por el cuerpo de una función demorada.")

# Declaration
add("KindUnifiersRemainUndetermined", "The compiler could not figure out every kind in this declaration (leftover `UNIF` markers internally).", "Kompilatorn kunde inte lista ut varje sort i denna deklaration (kvarvarande `UNIF` internt).", "El compilador no pudo determinar cada clase en esta declaración (marcadores `UNIF` internos).")
add("HintKindUnifiersRemainUndetermined", "Add kind annotations (`::` / `:::`) on type parameters or constructors so nothing stays ambiguous.", "Lägg till sortannoteringar (`::` / `:::`) på typparametrar eller konstruktorer så inget förblir tvetydigt.", "Añade anotaciones de clase (`::` / `:::`) en parámetros de tipo o constructores para que nada quede ambiguo.")

add("ConstructorUnifiersRemainUndetermined", "The compiler could not finish inferring every type argument in this declaration.", "Kompilatorn kunde inte sluta inferera varje typargument i denna deklaration.", "El compilador no pudo terminar de inferir cada argumento de tipo en esta declaración.")
add("HintConstructorUnifiersRemainUndetermined", "Spell out a few types on parameters or result types until the error disappears.", "Skriv ut några typer på parametrar eller resultattyper tills felet försvinner.", "Escribe algunos tipos en parámetros o en el resultado hasta que el error desaparezca.")

add("NonStrictlyPositiveDeclaration", "This datatype is not strictly positive, which Ur/Web rejects to keep logic sound.", "Denna datatyp är inte strengt positiv, vilket Ur/Web avvisar för att logiken ska vara sund.", "Este tipo de datos no es estrictamente positivo; Ur/Web lo rechaza para mantener la lógica sólida.")
add("HintNonStrictlyPositiveDeclaration", "Restructure so the recursive type does not appear to the left of an arrow inside itself.", "Omstrukturera så att den rekursiva typen inte står till vänster om en pil inuti sig själv.", "Reestructura para que el tipo recursivo no aparezca a la izquierda de una flecha dentro de sí mismo.")

add("TypeHoleFoundInternal", "TYPE HOLE (internal)\n\nThe elaborator left a type hole here: {0}\n\nThis usually means inference could not complete; try annotating the surrounding expression.", "TYP-HÅL (internt)\n\nElaboratorn lämnade ett typ-hår här: {0}\n\nDetta betyder ofta att inferensen inte fullföljdes; prova att annotera det omgivande uttrycket.", "AGUJERO DE TIPO (interno)\n\nEl elaborador dejó un agujero de tipo aquí: {0}\n\nSuele indicar que la inferencia no terminó; intenta anotar la expresión circundante.")

# Batch 2: optional file keeps the main script readable.
_SCRIPTS = Path(__file__).resolve().parent
for _extra in ("_catalog_batch2.py", "_catalog_rest.py"):
    _path = _SCRIPTS / _extra
    if _path.is_file():
        exec(
            compile(_path.read_text(encoding="utf-8"), str(_path), "exec"),
            {"add": add},
        )


def main() -> None:
    lines_ids = [
        "//! Auto-generated by scripts/gen_diagnostic_catalog.py — do not hand-edit.",
        "",
        "#[repr(u32)]",
        "#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]",
        "pub enum DiagnosticId {",
    ]
    for i, (name, _, _, _) in enumerate(CATALOG, start=1):
        lines_ids.append(f"    /// Catalog entry {i}.")
        lines_ids.append(f"    {name} = {i},")
    lines_ids.append("}")
    lines_ids.append("")
    with open("src/diagnostics/ids.rs", "w", encoding="utf-8") as f:
        f.write("\n".join(lines_ids))

    # template_tables.rs
    parts = [
        "//! Auto-generated template lookup — do not hand-edit.",
        "use super::ids::DiagnosticId;",
        "use super::locale::DiagnosticLocale;",
        "",
        "/// Localized template string for `id` (may contain `{0}`, …).",
        "pub fn diagnostic_template(id: DiagnosticId, locale: DiagnosticLocale) -> &'static str {",
        "    match locale {",
        "        DiagnosticLocale::En => template_en(id),",
        "        DiagnosticLocale::Sv => template_sv(id),",
        "        DiagnosticLocale::Es => template_es(id),",
        "    }",
        "}",
        "",
    ]
    for lang, idx in [("en", 1), ("sv", 2), ("es", 3)]:
        fname = f"template_{lang}"
        parts.append(f"fn template_{lang}(id: DiagnosticId) -> &'static str {{")
        parts.append("    match id {")
        for name, tup in zip([c[0] for c in CATALOG], CATALOG):
            parts.append(
                f"        DiagnosticId::{name} => {rust_string_literal(tup[idx])},"
            )
        parts.append("    }")
        parts.append("}")
        parts.append("")
    with open("src/diagnostics/template_tables.rs", "w", encoding="utf-8") as f:
        f.write("\n".join(parts))

    print(f"Wrote {len(CATALOG)} diagnostic ids.")


if __name__ == "__main__":
    main()
