import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.Compiler.Backend.Bvi.Syntax
import Flapjack.Misc.Sptree
import Flapjack.Compiler.Backend.BackendCommon.BvlStubs

namespace Flapjack.Compiler.Backend.BvlToBvi

/-- Complete source configuration. Both inline trees retain the distinct original
expression carriers and arities; HOL spt maps remain literal Spt trees.
The source initializer is separate and depends on backend_common's stub counts. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "config"]
structure Config where
  inlineSizeLimit : Nat
  expCut : Nat
  splitMainAtSeq : Bool
  nextName1 : Nat
  nextName2 : Nat
  nextName3 : Nat
  doTailrec : Bool
  doTmc : Bool
  inlines : Spt (Nat × Bvl.Exp)
  bviInlines : Spt (Nat × Bvi.Exp)

/-- Full source default, with the original shared stub-count chain. HOL's local
`num_stubs` abbreviation denotes `backend_common$bvl_num_stubs`; both inline
maps are the literal empty Spt trees, not arbitrary expression placeholders. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "default_config_def"]
def defaultConfig : Config :=
  { inlineSizeLimit := 10, expCut := 1000, splitMainAtSeq := true,
    nextName1 := Flapjack.bvlNumStubs + 1,
    nextName2 := Flapjack.bvlNumStubs + 2,
    nextName3 := Flapjack.bvlNumStubs + 3,
    doTailrec := true, doTmc := true, inlines := .ln, bviInlines := .ln }

end Flapjack.Compiler.Backend.BvlToBvi
