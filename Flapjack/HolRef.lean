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
checked same-module representation lemma and checker gate exist. The attribute
is inert for the kernel; it
exists so that

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
      lemma before the tag may be applied. -/
  listAsArray : Array String := #[]
  deriving Inhabited, Repr, BEq

open Lean

syntax (name := hol) "hol " str str (num)? ("(" "list_as_array" ":=" "[" ident,+ "]" ")")? : attr

private def checkedHolRef (path name : String) (line? : Option Nat := none)
    (listAsArray : Array String := #[]) : CoreM HolRef := do
  unless path.startsWith "cakeml/" && path.endsWith ".sml" do
    throwError "@[hol]: path must be a repository-relative `cakeml/...Script.sml` file, got {path}"
  if name.isEmpty || name.any Char.isWhitespace then
    throwError "@[hol]: declaration name must be a single HOL identifier, got {repr name}"
  if listAsArray.toList.eraseDups.length != listAsArray.size then
    throwError "@[hol]: list_as_array fields must be distinct"
  pure { path, name, line?, listAsArray }

initialize holRefAttribute : ParametricAttribute HolRef ←
  registerParametricAttribute {
    name := `hol
    descr := "original HOL4 declaration (file path and declaration name) ported by this Lean declaration"
    getParam := fun _ stx => do
      match stx with
      | `(attr| hol $path:str $name:str $line:num (list_as_array := [$fields:ident,*])) =>
          checkedHolRef path.getString name.getString (some line.getNat)
            (fields.getElems.map (fun field => field.getId.toString))
      | `(attr| hol $path:str $name:str (list_as_array := [$fields:ident,*])) =>
          checkedHolRef path.getString name.getString none
            (fields.getElems.map (fun field => field.getId.toString))
      | `(attr| hol $path:str $name:str $line:num) =>
          checkedHolRef path.getString name.getString (some line.getNat)
      | `(attr| hol $path:str $name:str) =>
          checkedHolRef path.getString name.getString
      | _ => throwError "@[hol]: expected `hol \"<cakeml path>\" \"<HOL declaration name>\" [line] [(list_as_array := [fields])]`"
  }

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
    let qualification := if ref.listAsArray.isEmpty then "" else
      s!" (list_as_array := [{String.intercalate ", " ref.listAsArray.toList}])"
    logInfo m!"{declName}  {ref.path}  {ref.name}{ref.line?.map (fun line => s!" :{line}") |>.getD ""}{qualification}"

end Flapjack
