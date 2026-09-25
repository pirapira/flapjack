import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.CrepLang
import Flapjack.FiniteMap.Basic
import Flapjack.Basis.Pure.MlString

/-!
Statement-exact port of HOL `crepSem$lookup_code_def`
(`cakeml/pancake/semantics/crepSemScript.sml:76-84`).

HOL keys the code map by `funname = ``:mlstring`` (`crepSemScript.sml:17`) and
stores argument/local values of type `'a word_lab` (`panSemScript.sml:17`).
The production `Flapjack.lookupCrepHolCode` uses Lean `String` keys and
`PanWordLab`, so it cannot carry the `lookup_code_def` tag.  This submodule
declares the exact carrier form over `Flapjack.Basis.Pure.MlString.MlString`
keys and the width-indexed `HolWordLab` values, and proves the kernel-checked
relationship to the production definition.
-/

namespace Flapjack

/-- The `lookup_code` code-map carrier: HOL `funname |-> (varname list # 'a crepLang$prog)`
(`crepSemScript.sml:17,23`), with the HOL `funname = mlstring` key and the word-indexed
program.  NOT YET EXACT: the map key is the faithful MlString carrier, but the
stored code value `CrepProg (BitVec width)` still uses `FunName := String` for its
`call`/`extCall` names (`Flapjack/Pancake/CrepLang.lean:60-62`), whereas HOL
`crepLang$prog.Call`/`ExtCall` carry `funname = mlstring`.  The exact code-value
carrier is tracked by `flapjack-4w9.1`; the exact lookup statement by
`flapjack-4w9.2`. -/
abbrev CrepCodeMapExact (width : Nat) : Type :=
  Flapjack.Basis.Pure.MlString.MlString → Option (List Nat × CrepProg (BitVec width))

/-- The exact `lookup_code` local-variable carrier: HOL `varname |-> 'a word_lab`. -/
abbrev CrepLocalsExact (width : Nat) : Type :=
  FiniteMap Nat (HolWordLab width)

/-- Structural port of HOL `crepSem$lookup_code_def` (`crepSemScript.sml:76-84`):
look the function up by its `mlstring` name, require a duplicate-free declared
parameter list of the same length as the supplied `word_lab` argument list, and
return the body together with the finite map `FEMPTY |++ ZIP (parameters, args)`.
The `len` argument is retained from the HOL signature, where the definition does
not inspect it.

NOT TAGGED (coordinator review HOLD on `f1e2a00be`, bead `flapjack-4w9`): the map
key and the `word_lab` argument/local carriers are exact, but the code value's
`CrepProg.call`/`.extCall` names are `FunName := String`, while HOL
`crepLang$prog.Call`/`ExtCall` carry `funname = mlstring`, so the transitive
code-value carrier is not exact.  The useful kernel-checked production bridge
below is kept, but no `@[hol]` tag is claimed.  Exact carrier: `flapjack-4w9.1`;
exact tagged statement: `flapjack-4w9.2`; executable routing: `flapjack-4w9.3`. -/
def lookupCodeHOL {width : Nat} [NeZero width]
    (code : CrepCodeMapExact width)
    (fname : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (HolWordLab width)) (_len : Nat) :
    Option (CrepProg (BitVec width) × CrepLocalsExact width) :=
  match FLOOKUP code fname with
  | none => none
  | some (parameters, body) =>
      if parameters.length = args.length ∧ parameters.Nodup
      then some (body, FUPDATE_LIST FEMPTY (parameters.zip args))
      else none

/-! ## Kernel-checked relationship to the production definition

The production `Flapjack.lookupCrepHolCode` (`CrepSem.lean`) uses `String` keys
and `PanWordLab` values.  We transport the exact code map by the byte-ranged
`toStringOfBytes` and transport the exact `word_lab` values by the checked
isomorphism `HolWordLab.toPanWordLab`; the two lookups then agree exactly. -/

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

/-- The production code map induced by an exact one, via the byte-ranged
`toStringOfBytes` key conversion. -/
def codeMapExactToProd {width : Nat} (code : CrepCodeMapExact width) :
    FunName → Option (List Nat × CrepProg (BitVec width)) :=
  fun name => code (Flapjack.Basis.Pure.MlString.ofString name)

/-- The exact code map induced by a production one, via the byte-ranged
`toStringOfBytes` key conversion. -/
def codeMapProdToExact {width : Nat}
    (code : FunName → Option (List Nat × CrepProg (BitVec width))) : CrepCodeMapExact width :=
  fun name => code (Flapjack.Basis.Pure.MlString.toStringOfBytes name)

/-- Transporting the empty finite map's codomain leaves it empty. -/
@[simp] theorem mapFiniteMap_empty {α β γ : Type} (g : β → γ) :
    mapFiniteMap g (FEMPTY : FiniteMap α β) = (FEMPTY : FiniteMap α γ) := by
  funext key
  rfl

/-- Zipping declared parameter names with `HolWordLab` arguments and then
projecting the values back to `PanWordLab` recovers the production zip. -/
theorem zip_holToPan {width : Nat} (names : List Nat)
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

/-- Kernel-checked bridge: on the exact code-map image of a production map and on
`PanWordLab` arguments transported by the checked isomorphism, the exact
`lookupCodeHOL` returns exactly the production `lookupCrepHolCode` result
(transporting the resulting `word_lab` locals back along the isomorphism). -/
theorem lookupCodeHOL_prodToExact {width : Nat} [NeZero width]
    (code : FunName → Option (List Nat × CrepProg (BitVec width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (PanWordLab (BitVec width))) (len : Nat) :
    (lookupCodeHOL (codeMapProdToExact code) fname (args.map PanWordLab.toHolWordLab) len).map
        (fun result => (result.1, mapFiniteMap HolWordLab.toPanWordLab result.2)) =
      lookupCrepHolCode code (Flapjack.Basis.Pure.MlString.toStringOfBytes fname) args len := by
  unfold lookupCodeHOL lookupCrepHolCode codeMapProdToExact
  simp only [FLOOKUP]
  generalize h : code (Flapjack.Basis.Pure.MlString.toStringOfBytes fname) = value
  cases value with
  | none => rfl
  | some pair =>
      obtain ⟨parameters, body⟩ := pair
      simp only [List.length_map]
      by_cases hcond : parameters.length = args.length ∧ parameters.Nodup <;>
        simp [hcond, mapFiniteMap_FUPDATE_LIST, zip_holToPan]

end Flapjack
