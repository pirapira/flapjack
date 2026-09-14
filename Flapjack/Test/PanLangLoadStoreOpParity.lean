import Flapjack.Compile

/-!
# Pancake load/store operation parity

The expected values are direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_load_store_op_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:300-313`.

The Lean result uses the existing `CrepMemOp` normalization used by the
compiler backend: `Load`/`Store` become `.load`/`.store`, while fixed-width
operations retain their width.
-/

namespace Flapjack.Test.PanLangLoadStoreOpParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:300-313 (load_op_def/store_op_def)"

def parityGuard : Bool :=
  loadMemOp .op8 == .load8 &&
  loadMemOp .op16 == .load16 &&
  loadMemOp .opW == .load &&
  loadMemOp .op32 == .load32 &&
  storeMemOp .op8 == .store8 &&
  storeMemOp .op16 == .store16 &&
  storeMemOp .opW == .store &&
  storeMemOp .op32 == .store32

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:300-313 (load_op_def/store_op_def)"
#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanLangLoadStoreOpParity
