import Flapjack.Pancake.PanToCrep.Compile

/-!
# Pancake load/store operation parity

The expected values are direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_load_store_op_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:300-313`.

The Lean result uses the reviewed tagged `loadMemOpHOL`/`storeMemOpHOL`
definitions over `OpSize`/`CrepMemOp`; the executable `compileProg` calls these
definitions directly. The eight direct HOL-EVAL rows are reproduced below, both
as `#guard` computations and as kernel-checked `rfl` equations.
-/

namespace Flapjack.Test.PanLangLoadStoreOpParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:300-313 (load_op_def/store_op_def)"

def parityGuard : Bool :=
  loadMemOpHOL .op8 == .load8 &&
  loadMemOpHOL .op16 == .load16 &&
  loadMemOpHOL .opW == .load &&
  loadMemOpHOL .op32 == .load32 &&
  storeMemOpHOL .op8 == .store8 &&
  storeMemOpHOL .op16 == .store16 &&
  storeMemOpHOL .opW == .store &&
  storeMemOpHOL .op32 == .store32

example : loadMemOpHOL .op8 = .load8 := rfl
example : loadMemOpHOL .op16 = .load16 := rfl
example : loadMemOpHOL .opW = .load := rfl
example : loadMemOpHOL .op32 = .load32 := rfl
example : storeMemOpHOL .op8 = .store8 := rfl
example : storeMemOpHOL .op16 = .store16 := rfl
example : storeMemOpHOL .opW = .store := rfl
example : storeMemOpHOL .op32 = .store32 := rfl

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:300-313 (load_op_def/store_op_def)"
#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanLangLoadStoreOpParity
