import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.CrepLang.Prog
import Flapjack.FiniteMap.Basic
import Flapjack.Basis.Pure.MlString

/-!
Exact port of HOL `crepSem$lookup_code_def`
(`cakeml/pancake/semantics/crepSemScript.sml:76-84`), together with a
kernel-checked relationship to the production `Flapjack.lookupCrepHolCode`.

HOL keys the code map by `funname = ``:mlstring`` (`crepSemScript.sml:17`),
stores `(varname list # 'a crepLang$prog)` values, and takes `'a word_lab`
argument/local values (`panSemScript.sml:17`). This submodule therefore uses the
faithful `MlString` key, the exact width-indexed `CrepProgHOL` code value
(`Flapjack/Pancake/CrepLang/Prog.lean`), and width-indexed `HolWordLab` values.
The production `Flapjack.lookupCrepHolCode` uses Lean `String` keys,
`CrepProg (BitVec width)`, and `PanWordLab`; the bridge
`lookupCodeHOL_exactToProd` transports the exact result back along
`crepProgOfHOL` and `HolWordLab.toPanWordLab`. The executed-path bridge
`lookupCrepRuntimeCode_exactImage` records that the runtime lookup on the
induced production map is exactly that image, with the caveat that textual
routing would require an `MlString`-keyed runtime code map.
-/

namespace Flapjack

/-- The exact `lookup_code` code-map carrier: HOL `funname |-> (varname list # 'a crepLang$prog)`
(`crepSemScript.sml:17,23`), with the faithful `funname = mlstring` key and the
exact width-indexed `CrepProgHOL` code value. -/
abbrev CrepCodeMapExact (width : Nat) [NeZero width] : Type :=
  Flapjack.Basis.Pure.MlString.MlString → Option (List Nat × CrepProgHOL width)

/-- The exact `lookup_code` local-variable carrier: HOL `varname |-> 'a word_lab`. -/
abbrev CrepLocalsExact (width : Nat) [NeZero width] : Type :=
  FiniteMap Nat (HolWordLab width)

/-- Exact port of HOL `crepSem$lookup_code_def` (`crepSemScript.sml:76-84`):
look the function up by its `mlstring` name, require a duplicate-free declared
parameter list of the same length as the supplied `word_lab` argument list, and
return the body together with the finite map `FEMPTY |++ ZIP (parameters, args)`.
The `len` argument is retained from the HOL signature, where the definition does
not inspect it. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "lookup_code_def"]
def lookupCodeHOL {width : Nat} [NeZero width]
    (code : CrepCodeMapExact width)
    (fname : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (HolWordLab width)) (_len : Nat) :
    Option (CrepProgHOL width × CrepLocalsExact width) :=
  match FLOOKUP code fname with
  | none => none
  | some (parameters, body) =>
      if parameters.length = args.length ∧ parameters.Nodup
      then some (body, FUPDATE_LIST FEMPTY (parameters.zip args))
      else none

/-! ## Kernel-checked relationship to the production definition

The production `Flapjack.lookupCrepHolCode` (`CrepSem.lean`) uses `String` keys
and `PanWordLab` values.  We transport the code map by the byte-ranged
`ofString`/`toStringOfBytes` key conversion and the code value by the checked
isomorphism `crepProgOfHOL`; the exact `word_lab` values are transported by
`HolWordLab.toPanWordLab`; the two lookups then agree exactly. -/

/-- Pointwise transport of a finite map's codomain along an option map. -/
def mapFiniteMap {α β γ : Type} (g : β → γ) (f : FiniteMap α β) : FiniteMap α γ :=
  fun key => (f key).map g

/-- Transporting a finite map's codomain commutes with `FUPDATE`. -/
theorem mapFiniteMap_FUPDATE [BEq α] (g : β → γ) (f : FiniteMap α β)
    (entry : α × β) :
    mapFiniteMap g (FUPDATE f entry) = FUPDATE (mapFiniteMap g f) (entry.1, g entry.2) := by
  funext key
  simp only [mapFiniteMap, FUPDATE]
  by_cases h : entry.1 == key <;> simp [h]

/-- Transporting a finite map's codomain commutes with `FUPDATE_LIST`. -/
theorem mapFiniteMap_FUPDATE_LIST [BEq α] (g : β → γ) (f : FiniteMap α β)
    (entries : List (α × β)) :
    mapFiniteMap g (FUPDATE_LIST f entries) =
      FUPDATE_LIST (mapFiniteMap g f) (entries.map (fun entry => (entry.1, g entry.2))) := by
  unfold FUPDATE_LIST
  induction entries generalizing f with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [← mapFiniteMap_FUPDATE (g := g) (f := f) entry]
      exact ih (FUPDATE f entry)

/-- The production code map induced by an exact one: the byte-ranged
`ofString` key conversion and the checked `crepProgOfHOL` code-value
isomorphism. -/
def codeMapExactToProd {width : Nat} [NeZero width] (code : CrepCodeMapExact width) :
    FunName → Option (List Nat × CrepProg (BitVec width)) :=
  fun name => (code (Flapjack.Basis.Pure.MlString.ofString name)).map
    (fun entry => (entry.1, crepProgOfHOL entry.2))

/-- The exact code map induced by a production one, via the byte-ranged
`toStringOfBytes` key conversion and the checked `crepProgToHOL` code-value
isomorphism (which requires byte-ranged name fields for an exact roundtrip). -/
def codeMapProdToExact {width : Nat} [NeZero width]
    (code : FunName → Option (List Nat × CrepProg (BitVec width))) : CrepCodeMapExact width :=
  fun name => (code (Flapjack.Basis.Pure.MlString.toStringOfBytes name)).map
    (fun entry => (entry.1, crepProgToHOL entry.2))

/-- Transporting the empty finite map's codomain leaves it empty. -/
@[simp] theorem mapFiniteMap_empty {α β γ : Type} (g : β → γ) :
    mapFiniteMap g (FEMPTY : FiniteMap α β) = (FEMPTY : FiniteMap α γ) := by
  funext key
  rfl

/-- Zipping declared parameter names with `HolWordLab` arguments and then
projecting the values back to `PanWordLab` recovers the production zip. -/
theorem zip_holToPan {width : Nat} [NeZero width] (names : List Nat)
    (args : List (PanWordLab (BitVec width))) :
    ((names.zip (args.map PanWordLab.toHolWordLab)).map
        (fun entry => (entry.1, HolWordLab.toPanWordLab entry.2))) = names.zip args := by
  induction names generalizing args with
  | nil => cases args <;> rfl
  | cons name names ih =>
      cases args with
      | nil => rfl
      | cons arg args =>
          simp only [List.map_cons, List.zip_cons_cons]
          rw [ih args]
          simp

/-- Kernel-checked bridge: on the exact code map and on `PanWordLab` arguments
transported by the checked isomorphism, the exact `lookupCodeHOL` returns
exactly the production `lookupCrepHolCode` applied to the induced production
map `codeMapExactToProd code`, transporting the returned `word_lab` locals and
the code-value body back along the checked isomorphisms. -/
theorem lookupCodeHOL_exactToProd {width : Nat} [NeZero width]
    (code : CrepCodeMapExact width)
    (fname : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (PanWordLab (BitVec width))) (len : Nat) :
    (lookupCodeHOL code fname (args.map PanWordLab.toHolWordLab) len).map
        (fun result => (crepProgOfHOL result.1, mapFiniteMap HolWordLab.toPanWordLab result.2)) =
      lookupCrepHolCode (codeMapExactToProd code) (Flapjack.Basis.Pure.MlString.toStringOfBytes fname)
        args len := by
  unfold lookupCodeHOL lookupCrepHolCode codeMapExactToProd
  simp only [FLOOKUP]
  rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes fname]
  generalize h : code fname = value
  cases value with
  | none => rfl
  | some pair =>
      obtain ⟨parameters, body⟩ := pair
      simp only [List.length_map]
      by_cases hcond : parameters.length = args.length ∧ parameters.Nodup <;>
        simp [hcond, mapFiniteMap_FUPDATE_LIST, zip_holToPan]

/-! ## Executed-path bridge

The executed crepSem interpreter performs its code lookup through
`Flapjack.lookupCrepRuntimeCode` (`CrepSem.lean`), which is keyed by the
production `FunName = String` and consumes raw `BitVec width` argument values.
A full textual route through `lookupCodeHOL` would require changing the runtime
code map (`CrepRuntimeState.code` / `caller.code`) to the `MlString` key, which
is a state-representation change touching the whole interpreter and its proof
surface. The theorem below instead gives a kernel-checked bridge: on the
production code map induced by an exact one (`codeMapExactToProd`), the executed
lookup is exactly the image of the exact `lookupCodeHOL`. This establishes the
executed path is bridge-equal to the reviewed exact carrier, with the documented
caveat that routing is not textual. -/

/-- Kernel-checked executed-path bridge: the runtime code lookup on the
production map induced by an exact one returns exactly the `codeMapExactToProd`
image of the exact `lookupCodeHOL` result. -/
theorem lookupCrepRuntimeCode_exactImage {width : Nat} [NeZero width]
    (code : CrepCodeMapExact width)
    (fname : Flapjack.Basis.Pure.MlString.MlString)
    (values : List (BitVec width)) (len : Nat) :
    lookupCrepRuntimeCode (Flapjack.Basis.Pure.MlString.toStringOfBytes fname) values
        (codeMapExactToProd code) =
      (lookupCodeHOL code fname ((values.map PanWordLab.word).map PanWordLab.toHolWordLab) len).map
        (fun result => (crepProgOfHOL result.1, mapFiniteMap HolWordLab.toPanWordLab result.2)) := by
  rw [lookupCrepRuntimeCode_eq_lookupCrepHolCode]
  exact (lookupCodeHOL_exactToProd code fname (values.map PanWordLab.word) len).symm

end Flapjack
