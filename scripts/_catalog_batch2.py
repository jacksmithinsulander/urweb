# Executed by gen_diagnostic_catalog.py with add() in scope.

# --- Signature (elaboration_errors) ---
add(
    "UnboundSignatureName",
    "I do not know what the signature name `{0}` refers to in this context.",
    "Jag vet inte vad signaturnamnet `{0}` avser i detta sammanhang.",
    "No sé a qué se refiere el nombre de firma `{0}` en este contexto.",
)
add(
    "HintUnboundSignatureName",
    "Declare it with `signature S = ...` or qualify it with the module path you meant.",
    "Deklarera med `signature S = ...` eller kvalificera med modulsökvägen du menade.",
    "Declárala con `signature S = ...` o califícala con la ruta de módulo que quisiste.",
)
add(
    "UnmatchedSignatureItem",
    "This implementation is missing something the signature requires, or has an extra item.\n\nProblem item: {0}",
    "Implementationen saknar något signaturen kräver, eller har ett extra objekt.\n\nProblemobjekt: {0}",
    "A la implementación le falta algo que exige la firma, o tiene un ítem de más.\n\nÍtem problemático: {0}",
)
add(
    "HintUnmatchedSignatureItem",
    "Compare your `structure ... : SIG =` body line‑by‑line with the `.urs` file or `signature` definition.",
    "Jämför din `structure ... : SIG =`-kropp rad för rad med `.urs`-filen eller `signature`-definitionen.",
    "Compara el cuerpo de `structure ... : SIG =` línea a línea con el `.urs` o la definición `signature`.",
)
add(
    "SignatureItemKindUnificationFailed",
    "Kind unification failure in signature matching: have {0} (kind {1}), need {2} (kind {3}); {4}",
    "Sorter misslyckades vid signaturmatchning: har {0} (sort {1}), behöver {2} (sort {3}); {4}",
    "Fallo de unificación de clases al casar la firma: hay {0} (clase {1}), se necesita {2} (clase {3}); {4}",
)
add(
    "SignatureItemConstructorUnificationFailed",
    "Constructor unification failure in signature matching: have {0} (con {1}), need {2} (con {3}); {4}",
    "Konstruktorunifiering misslyckades vid signaturmatchning: har {0} (kon {1}), behöver {2} (kon {3}); {4}",
    "Fallo de unificación de constructores al casar la firma: hay {0} (con {1}), se necesita {2} (con {3}); {4}",
)
add(
    "SignatureItemDatatypeSpecificationsMismatch",
    "Mismatched 'datatype' specifications: {0} vs {1}{2}",
    "Olika `datatype`-specifikationer: {0} mot {1}{2}",
    "Especificaciones `datatype` incompatibles: {0} frente a {1}{2}",
)
add(
    "IncompatibleSignatureShapes",
    "Incompatible signatures: {0} vs {1}",
    "Inkompatibla signaturer: {0} mot {1}",
    "Firmas incompatibles: {0} frente a {1}",
)
add(
    "WhereClauseFieldUnavailable",
    "The `where` clause mentions `{0}`, but that field is not available on this record.",
    "`where`-satsen nämner `{0}`, men det fältet finns inte på denna post.",
    "La cláusula `where` menciona `{0}`, pero ese campo no está disponible en este registro.",
)
add(
    "HintWhereClauseFieldUnavailable",
    "Check the label spelling and make sure the record type in the signature actually exposes that field.",
    "Kontrollera etikettstavningen och att posttypen i signaturen verkligen exponerar fältet.",
    "Revisa la ortografía de la etiqueta y que el tipo de registro en la firma exponga ese campo.",
)
add(
    "WhereClauseKindMismatch",
    "Wrong kind for 'where': have {0}, need {1}; {2}",
    "Fel sort för `where`: har {0}, behöver {1}; {2}",
    "Clase incorrecta para `where`: hay {0}, se necesita {1}; {2}",
)
add(
    "SignatureNotValidForInclude",
    "This signature cannot be used with `include` here.",
    "Denna signatur kan inte användas med `include` här.",
    "Esta firma no puede usarse con `include` aquí.",
)
add(
    "HintSignatureNotValidForInclude",
    "`include` needs a sealed, compatible signature shape; try inlining items or adjusting the interface.",
    "`include` kräver en förseglad, kompatibel signaturform; prova att infoga objekt eller justera gränssnittet.",
    "`include` necesita una forma de firma sellada y compatible; prueba a insertar ítems o ajustar la interfaz.",
)
add(
    "DuplicateConstructorNameInSignature",
    "The constructor `{0}` is declared twice in the same signature.",
    "Konstruktorn `{0}` är deklarerad två gånger i samma signatur.",
    "El constructor `{0}` está declarado dos veces en la misma firma.",
)
add(
    "HintDuplicateConstructorNameInSignature",
    "Rename or merge the duplicates so each datatype constructor name is unique in the interface.",
    "Byt namn eller slå ihop dubbletter så varje datatypskonstruktor är unik i gränssnittet.",
    "Renombra o fusiona duplicados para que cada constructor sea único en la interfaz.",
)
add(
    "DuplicateValueNameInSignature",
    "The value `{0}` is declared twice in the same signature.",
    "Värdet `{0}` är deklarerat två gånger i samma signatur.",
    "El valor `{0}` está declarado dos veces en la misma firma.",
)
add(
    "HintDuplicateValueNameInSignature",
    "Remove the duplicate `val` line or give one of the bindings a different name.",
    "Ta bort den dubbla `val`-raden eller ge en av bindningarna ett annat namn.",
    "Elimina la línea `val` duplicada o dale otro nombre a uno de los enlaces.",
)
add(
    "DuplicateNestedSignatureNameInSignature",
    "The nested signature `{0}` appears twice.",
    "Den nästlade signaturen `{0}` förekommer två gånger.",
    "La firma anidada `{0}` aparece dos veces.",
)
add(
    "HintDuplicateNestedSignatureNameInSignature",
    "Each nested `signature` name inside an interface must be unique.",
    "Varje nästlad `signature` inuti ett gränssnitt måste vara unik.",
    "Cada `signature` anidada dentro de la interfaz debe ser única.",
)
add(
    "DuplicateStructureNameInSignature",
    "The structure `{0}` is declared twice in the same signature.",
    "Strukturen `{0}` är deklarerad två gånger i samma signatur.",
    "La estructura `{0}` está declarada dos veces en la misma firma.",
)
add(
    "HintDuplicateStructureNameInSignature",
    "Drop the duplicate `structure` item or rename one of the modules.",
    "Ta bort det dubbla `structure`-objektet eller byt namn på en av modulerna.",
    "Quita el ítem `structure` duplicado o renombra uno de los módulos.",
)
add(
    "SignatureNotValidForOpenConstraints",
    "This signature cannot be used with `open constraints`.",
    "Denna signatur kan inte användas med `open constraints`.",
    "Esta firma no puede usarse con `open constraints`.",
)
add(
    "HintSignatureNotValidForOpenConstraints",
    "Simplify the interface or satisfy the constraints earlier; `open constraints` expects a specific shape.",
    "Förenkla gränssnittet eller tillfredsställ villkoren tidigare; `open constraints` förväntar sig en specifik form.",
    "Simplifica la interfaz o cumple las restricciones antes; `open constraints` espera una forma concreta.",
)

# Structure elaboration
add(
    "UnboundStructureVariable",
    "I cannot find a structure or functor named `{0}` to use here.",
    "Jag hittar ingen struktur eller funktor `{0}` att använda här.",
    "No encuentro una estructura o functor `{0}` para usar aquí.",
)
add(
    "HintUnboundStructureVariable",
    "Define it, `open` the right module, or use the full `Path.to.Structure` prefix.",
    "Definiera den, `open` rätt modul, eller använd hela prefixet `Path.to.Structure`.",
    "Defínela, haz `open` del módulo correcto o usa el prefijo completo `Path.to.Structure`.",
)
add(
    "AppliedNonFunctor",
    "You are applying something that is not a functor (no `functor (...) : ...` shape).",
    "Du applicerar något som inte är en funktor (ingen `funktor (...): ...`-form).",
    "Estás aplicando algo que no es un functor (no tiene forma `functor (...) : ...`).",
)
add(
    "HintAppliedNonFunctor",
    "Only functors accept `F(arg)` arguments; ordinary structures are referenced by name alone.",
    "Bara funktorer tar `F(arg)`-argument; vanliga strukturer refereras bara med namn.",
    "Solo los functores aceptan argumentos `F(arg)`; las estructuras normales se citan solo por nombre.",
)
add(
    "FunctorRebindingAttempt",
    "Functors cannot be rebound like ordinary values.",
    "Funktorer kan inte bindas om som vanliga värden.",
    "Los functores no se pueden reenlazar como valores ordinarios.",
)
add(
    "HintFunctorRebindingAttempt",
    "Use a fresh functor name or restructure the `structure` / `functor` binding.",
    "Använd ett nytt funktornamn eller omstrukturera `structure`-/`functor`-bindningen.",
    "Usa un nombre de functor nuevo o reestructura el enlace `structure` / `functor`.",
)
add(
    "StructureNotOpenable",
    "`open` cannot expose this structure's contents.",
    "`open` kan inte exponera denna strukturs innehåll.",
    "`open` no puede exponer el contenido de esta estructura.",
)
add(
    "HintStructureNotOpenable",
    "It may be sealed, abstract, or incompatible with `open`; qualify names instead.",
    "Den kan vara förseglad, abstrakt eller inkompatibel med `open`; kvalificera namn i stället.",
    "Puede estar sellada, ser abstracta o ser incompatible con `open`; califica los nombres.",
)
add(
    "ValTypeKindIsNotType",
    "'val' type kind is not 'Type': kind {0}, subkind 1 {1}, subkind 2 {2}; {3}",
    "`val`-typsort är inte `Type`: sort {0}, delsort 1 {1}, delsort 2 {2}; {3}",
    "La clase del tipo `val` no es `Type`: clase {0}, subclase 1 {1}, subclase 2 {2}; {3}",
)
add(
    "DuplicateDatatypeConstructorNameInGroup",
    "The datatype constructor `{0}` is defined twice in this declaration group.",
    "Datatypskonstruktorn `{0}` är definierad två gånger i denna deklarationsgrupp.",
    "El constructor `{0}` del tipo de datos está definido dos veces en este grupo de declaraciones.",
)
add(
    "HintDuplicateDatatypeConstructorNameInGroup",
    "Each variant name must be unique within the same `datatype` declaration.",
    "Varje variantnamn måste vara unikt inom samma `datatype`-deklaration.",
    "Cada nombre de variante debe ser único en la misma declaración `datatype`.",
)
add(
    "ImportingNonDatatypeAsDatatype",
    "Only real `datatype` definitions can be imported as datatypes here.",
    "Bara riktiga `datatype`-definitioner kan importeras som datatyper här.",
    "Solo las definiciones `datatype` reales pueden importarse como tipos de datos aquí.",
)
add(
    "HintImportingNonDatatypeAsDatatype",
    "Check that you are referencing the datatype name, not a type synonym or structure.",
    "Kontrollera att du refererar datatypnamnet, inte en typsynonym eller struktur.",
    "Comprueba que citas el nombre del tipo de datos, no un sinónimo o una estructura.",
)

