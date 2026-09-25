import Lean

/-!
# `@[hol ...]`: cross-reference to the original HOL4 declaration

Every Lean theorem or definition that ports a declaration from the CakeML/HOL4
development carries

    @[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"]

naming the HOL source file (repository-relative, inside the `cakeml`
submodule) and the exact HOL declaration name (`Theorem`, `Triviality`,
`Definition`, `Datatype`, ...). When a script declares the same name twice,
append its source line, e.g. `@[hol "...Script.sml" "name" 123]`. The
experimental `list_as_array` qualifier records HOL list fields represented by
Lean arrays, e.g. `@[hol "...Script.sml" "dec_deg_def"
(list_as_array := [degrees])]`. It does not authorize a qualified tag until a
checked same-module representation lemma and checker gate exist. The
`names_as_string` qualifier records a narrowly reviewed HOL `mlstring` name
represented by Lean `String`. Its identifiers can name parameters or other
uses, not just structure fields, e.g.
`@[hol "...Script.sml" "fresh_name_def" (names_as_string := [name])]`.
The theorem-map reviewer classifies each identifier as equality/map-key-only
or byte-observable. Byte-observable identifiers are the explicit subset
`(names_as_string_boundary := [name])` and require a same-module checked
`holMlStringWitness_<LeanDeclaration>` whose conclusion establishes
`NameRanged` for the declaration's output. The witness may require
`NameRanged` input premises; the checker verifies only its name/result shape,
while Lean checks its proof and source review checks that the executed path
supplies its premises.
The `fmap_as_finite_support` qualifier records structure fields whose HOL
`|->` finite map is represented by the reviewed canonical Lean translation
`HolFiniteMapExact` (a `lookup` function together with a `finiteSupport`
proposition). It names fields, e.g.
`@[hol "...Script.sml" "set_var_def" (fmap_as_finite_support := [locals])]`.
The checker requires each named field to be declared in a same-module
structure, to actually use the `HolFiniteMapExact` carrier (a raw
`α → Option β` map is ineligible), and requires the same-module canonical
witness `holFmapAsFiniteSupportWitness` (extensionality plus
`toExact`/`ofExact` roundtrips). It is a representation statement only and
does not authorize changed quantifiers, hypotheses, conclusions, `BEq` side
conditions, or word-model differences.
It does not authorize any other carrier, statement, or behavior difference.
Qualified declarations remain subject to the checker and reviewed manifest.
The attribute is inert for the kernel; it exists so that

* a reader can find the original statement without a lookup table, whatever
  the Lean name is;
* `scripts/check-hol-refs.py` can verify that the cited file and declaration
  exist, and emit the HOL-to-Lean mapping;
* `#hol_refs` can list every cross-referenced declaration in scope.

When one HOL theorem is split across several Lean declarations (for example,
one per `evaluate` case of `pc_compile_correct`), every piece carries the same
attribute.  The rules for using it are in `AGENTS.md`.
-/

namespace Flapjack

/-- Location of the original HOL4 declaration. -/
structure HolRef where
  /-- Repository-relative path of the HOL script, e.g.
      `cakeml/pancake/proofs/pan_to_crepProofScript.sml`. -/
  path : String
  /-- Exact HOL declaration name, e.g. `pc_compile_correct`. -/
  name : String
  /-- Source line, required when the HOL script declares this name more than once. -/
  line? : Option Nat := none
  /-- HOL list fields represented by arrays in this Lean port.  An empty array
      denotes an exact port; qualified ports require a checked representation
      lemma before the tag may be applied. Each named field must be declared in
      a same-module structure and have a checked theorem named
      `holListArrayWitness_<field>` whose conclusion relates that field to a HOL
      list through `RepresentsHOLNodeList`, without assuming that relation in
      the witness premises. The reference checker validates this shape; it does
      not independently prove source-to-Lean semantic correspondence. -/
  listAsArray : Array String := #[]
  /-- Lean identifiers whose `String` carrier represents HOL `mlstring` names.
      Identifiers need not be structure fields. The manifest reviewer
      classifies each as equality/map-key-only or byte-observable. For a
      byte-observable identifier, a same-module
      `holMlStringWitness_<LeanDeclaration>` theorem must establish `NameRanged`
      for the declaration's output; input `NameRanged` premises are allowed.
      The checker checks only the witness name/result shape, not source
      correspondence or executed-path premise discharge. -/
  namesAsString : Array String := #[]
  /-- Subset of `namesAsString` identifiers classified by source review as
      byte-observable; these require a same-module checked witness. -/
  namesAsStringBoundary : Array String := #[]
  /-- Structure fields whose HOL `|->` finite-map carrier is represented by the
      reviewed canonical translation `HolFiniteMapExact`. Each named field must
      be a field of a same-module structure whose declared type uses
      `HolFiniteMapExact` (a raw `α → Option β` map is ineligible), and the
      module must contain the checked canonical witness
      `holFmapAsFiniteSupportWitness`. This is a representation statement only;
      it does not authorize changed hypotheses, results, `BEq` side conditions,
      or word-model differences. -/
  fmapAsFiniteSupport : Array String := #[]
  deriving Inhabited, Repr, BEq

open Lean

declare_syntax_cat holQualifier
syntax "(" "list_as_array" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "names_as_string" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "names_as_string_boundary" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "fmap_as_finite_support" ":=" "[" ident,+ "]" ")" : holQualifier
syntax (name := hol) "hol " str str (num)? holQualifier* : attr

private def checkedHolRef (path name : String) (line? : Option Nat := none)
    (listAsArray namesAsString namesAsStringBoundary fmapAsFiniteSupport : Array String := #[]) : CoreM HolRef := do
  unless path.startsWith "cakeml/" && path.endsWith ".sml" do
    throwError "@[hol]: path must be a repository-relative `cakeml/...Script.sml` file, got {path}"
  if name.isEmpty || name.any Char.isWhitespace then
    throwError "@[hol]: declaration name must be a single HOL identifier, got {repr name}"
  if listAsArray.toList.eraseDups.length != listAsArray.size then
    throwError "@[hol]: list_as_array fields must be distinct"
  if namesAsString.toList.eraseDups.length != namesAsString.size then
    throwError "@[hol]: names_as_string identifiers must be distinct"
  if namesAsStringBoundary.toList.eraseDups.length != namesAsStringBoundary.size then
    throwError "@[hol]: names_as_string_boundary identifiers must be distinct"
  unless namesAsStringBoundary.all namesAsString.contains do
    throwError "@[hol]: names_as_string_boundary identifiers must also appear in names_as_string"
  if fmapAsFiniteSupport.toList.eraseDups.length != fmapAsFiniteSupport.size then
    throwError "@[hol]: fmap_as_finite_support fields must be distinct"
  pure { path, name, line?, listAsArray, namesAsString, namesAsStringBoundary, fmapAsFiniteSupport }

private def parseHolQualifier (stx : Syntax) : CoreM (String × Array String) := do
  match stx with
  | `(holQualifier| (list_as_array := [$fields:ident,*])) =>
      pure ("list_as_array", fields.getElems.map (fun field => field.getId.eraseMacroScopes.toString))
  | `(holQualifier| (names_as_string := [$names:ident,*])) =>
      pure ("names_as_string", names.getElems.map (fun field => field.getId.eraseMacroScopes.toString))
  | `(holQualifier| (names_as_string_boundary := [$names:ident,*])) =>
      pure ("names_as_string_boundary", names.getElems.map (fun field => field.getId.eraseMacroScopes.toString))
  | `(holQualifier| (fmap_as_finite_support := [$fields:ident,*])) =>
      pure ("fmap_as_finite_support", fields.getElems.map (fun field => field.getId.eraseMacroScopes.toString))
  | _ => throwError "@[hol]: malformed qualifier"

private def parseHolRefAttribute (stx : Syntax) : CoreM HolRef := do
  let parse path name line? qualifiers := do
    let mut listAsArray : Array String := #[]
    let mut namesAsString : Array String := #[]
    let mut namesAsStringBoundary : Array String := #[]
    let mut fmapAsFiniteSupport : Array String := #[]
    for qualifier in qualifiers do
      let (kind, fields) ← parseHolQualifier qualifier
      if kind == "list_as_array" then listAsArray := listAsArray ++ fields
      else if kind == "names_as_string" then namesAsString := namesAsString ++ fields
      else if kind == "names_as_string_boundary" then namesAsStringBoundary := namesAsStringBoundary ++ fields
      else fmapAsFiniteSupport := fmapAsFiniteSupport ++ fields
    checkedHolRef path name line? listAsArray namesAsString namesAsStringBoundary fmapAsFiniteSupport
  match stx with
  | `(attr| hol $path:str $name:str $line:num $qualifiers:holQualifier*) =>
      parse path.getString name.getString (some line.getNat) qualifiers
  | `(attr| hol $path:str $name:str $qualifiers:holQualifier*) =>
      parse path.getString name.getString none qualifiers
  | _ => throwError "@[hol]: expected `hol \"<cakeml path>\" \"<HOL declaration name>\" [line] [(list_as_array := [fields])] [(names_as_string := [fields])]`"

initialize holRefAttribute : ParametricAttribute HolRef ←
  registerParametricAttribute {
    name := `hol
    descr := "original HOL4 declaration (file path and declaration name) ported by this Lean declaration"
    getParam := fun _ stx => parseHolRefAttribute stx
  }

private def HolRef.qualifierSuffix (ref : HolRef) : String :=
  let listAsArray := if ref.listAsArray.isEmpty then "" else
    s!" (list_as_array := [{String.intercalate ", " ref.listAsArray.toList}])"
  let namesAsString := if ref.namesAsString.isEmpty then "" else
    s!" (names_as_string := [{String.intercalate ", " ref.namesAsString.toList}])"
  let namesAsStringBoundary := if ref.namesAsStringBoundary.isEmpty then "" else
    s!" (names_as_string_boundary := [{String.intercalate ", " ref.namesAsStringBoundary.toList}])"
  let fmapAsFiniteSupport := if ref.fmapAsFiniteSupport.isEmpty then "" else
    s!" (fmap_as_finite_support := [{String.intercalate ", " ref.fmapAsFiniteSupport.toList}])"
  listAsArray ++ namesAsString ++ namesAsStringBoundary ++ fmapAsFiniteSupport

/-! Parser regressions for the original syntax, each qualifier alone, and both
qualifiers together. These elaborate temporary syntax values only; they do not
add test declarations to the HOL-reference inventory. -/
run_cmd do
  let plainSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname" 7)
  let plain ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute plainSyntax)
  unless plain.line? == some 7 && plain.listAsArray.isEmpty && plain.namesAsString.isEmpty &&
      plain.namesAsStringBoundary.isEmpty do
    throwError "@[hol] unqualified syntax regression"
  let listSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname" (list_as_array := [fields]))
  let listRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute listSyntax)
  unless listRef.listAsArray == #["fields"] && listRef.namesAsString.isEmpty &&
      listRef.namesAsStringBoundary.isEmpty do
    throwError "@[hol] list_as_array syntax regression"
  let namesSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname" (names_as_string := [name]))
  let namesRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute namesSyntax)
  unless namesRef.listAsArray.isEmpty && namesRef.namesAsString == #["name"] &&
      namesRef.namesAsStringBoundary.isEmpty do
    throwError "@[hol] names_as_string syntax regression"
  let bothSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname"
    9 (list_as_array := [fields]) (names_as_string := [name, fieldName]))
  let both ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute bothSyntax)
  unless both.line? == some 9 && both.listAsArray == #["fields"] &&
      both.namesAsString == #["name", "fieldName"] && both.namesAsStringBoundary.isEmpty do
    throwError "@[hol] combined qualifier syntax regression"
  unless HolRef.qualifierSuffix both ==
      " (list_as_array := [fields]) (names_as_string := [name, fieldName])" do
    throwError "@[hol] #hol_refs qualifier-output regression"
  let boundarySyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname"
    (names_as_string := [name, generated]) (names_as_string_boundary := [generated]))
  let boundaryRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute boundarySyntax)
  unless boundaryRef.namesAsString == #["name", "generated"] &&
      boundaryRef.namesAsStringBoundary == #["generated"] &&
      HolRef.qualifierSuffix boundaryRef ==
        " (names_as_string := [name, generated]) (names_as_string_boundary := [generated])" do
    throwError "@[hol] names_as_string_boundary syntax regression"
  let duplicateSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname"
    (names_as_string := [name, name]))
  let duplicateRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute duplicateSyntax
      pure false
    catch _ => pure true
  unless duplicateRejected do
    throwError "@[hol] duplicate names_as_string identifiers must be rejected"
  let boundaryOutsideSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname"
    (names_as_string := [name]) (names_as_string_boundary := [generated]))
  let boundaryOutsideRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute boundaryOutsideSyntax
      pure false
    catch _ => pure true
  unless boundaryOutsideRejected do
    throwError "@[hol] boundary identifiers outside names_as_string must be rejected"
  let fmapSyntax ← `(attr| hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"
    (fmap_as_finite_support := [locals, globals]))
  let fmapRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute fmapSyntax)
  unless fmapRef.fmapAsFiniteSupport == #["locals", "globals"] &&
      HolRef.qualifierSuffix fmapRef ==
        " (fmap_as_finite_support := [locals, globals])" do
    throwError "@[hol] fmap_as_finite_support syntax regression"
  let fmapDuplicateSyntax ← `(attr| hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"
    (fmap_as_finite_support := [locals, locals]))
  let fmapDuplicateRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute fmapDuplicateSyntax
      pure false
    catch _ => pure true
  unless fmapDuplicateRejected do
    throwError "@[hol] duplicate fmap_as_finite_support fields must be rejected"

/-- The HOL cross-reference attached to `declName`, if any. -/
def HolRef.get? (env : Environment) (declName : Name) : Option HolRef :=
  holRefAttribute.getParam? env declName

/-- Every declaration carrying `@[hol ...]` in the current environment, from the
    current module and from imported modules. -/
def HolRef.all (env : Environment) : Array (Name × HolRef) := Id.run do
  let mut result : Array (Name × HolRef) := #[]
  let (_, current) := holRefAttribute.ext.getState env
  result := current.foldl (fun acc declName ref => acc.push (declName, ref)) result
  for module in holRefAttribute.ext.toEnvExtension.getState env |>.importedEntries do
    for entry in module do
      result := result.push entry
  return result.qsort (fun left right => Name.lt left.1 right.1)

/-- `#hol_refs` prints every `@[hol]`-tagged declaration visible here as
    `<lean name>  <hol path>  <hol name> [:line]`. -/
syntax (name := holRefsCmd) "#hol_refs" : command

open Elab Command in
@[command_elab holRefsCmd] def elabHolRefs : CommandElab := fun _ => do
  let env ← getEnv
  for (declName, ref) in HolRef.all env do
    logInfo m!"{declName}  {ref.path}  {ref.name}{ref.line?.map (fun line => s!" :{line}") |>.getD ""}{HolRef.qualifierSuffix ref}"

end Flapjack
