import Flapjack.CrepeSemantics

/-!
Exact type boundary for CakeML Pancake `crepSem` globals.

The HOL state stores `5 word |-> word_lab` at
`cakeml/pancake/semantics/crepSemScript.sml:20-31`; the Lean production state
uses the extensionally equivalent function map `BitVec 5 -> Option (PanWordLab α)`.
The separate address and cell types are also used by `CrepRuntimeState`.
-/

namespace Flapjack

abbrev CrepGlobalAddress := BitVec 5

/-- HOL-shaped global cells keyed by the fixed-width `LoadGlob` address. -/
structure CrepGlobalState (α : Type u) where
  globals : CrepGlobalAddress → Option (PanWordLab α)

/-- `crepSem$eval (LoadGlob address)` reads the word-labeled cell. -/
def evalCrepGlobalLookup (globals : CrepGlobalAddress → Option (PanWordLab α))
    (address : CrepGlobalAddress) : Option (PanWordLab α) :=
  globals address

/-- `crepSem$set_globals` updates the fixed-width map and retains the
    `word_lab` wrapper. -/
def storeCrepGlobal (globals : CrepGlobalAddress → Option (PanWordLab α))
    (address : CrepGlobalAddress) (value : PanWordLab α) :
    CrepGlobalAddress → Option (PanWordLab α) :=
  fun current => if current == address then some value else globals current

@[simp] theorem evalCrepGlobalLookup_store_same
    (globals : CrepGlobalAddress → Option (PanWordLab α))
    (address : CrepGlobalAddress) (value : PanWordLab α) :
    evalCrepGlobalLookup (storeCrepGlobal globals address value) address = some value := by
  simp [evalCrepGlobalLookup, storeCrepGlobal]

@[simp] theorem evalCrepGlobalLookup_store_other
    (globals : CrepGlobalAddress → Option (PanWordLab α))
    (address other : CrepGlobalAddress) (value : PanWordLab α)
    (hne : other ≠ address) :
    evalCrepGlobalLookup (storeCrepGlobal globals address value) other = globals other := by
  simp [evalCrepGlobalLookup, storeCrepGlobal, beq_iff_eq, hne]

end Flapjack
