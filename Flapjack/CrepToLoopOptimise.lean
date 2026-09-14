import Flapjack.CrepToLoop
import Flapjack.LoopAnalysis

namespace Flapjack

/-! The optimised Crepe-to-Loop entry point corresponding to
    `crep_to_loop$ocompile` (`crep_to_loopScript.sml:216`). -/
def oCompile [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) (program : CrepProg α) :
    LoopProg α :=
  loopLiveOptimise (compileCrepToLoop context live program)

theorem oCompile_skip [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) :
    oCompile context live (.skip : CrepProg α) = .mark .skip := by
  simp [oCompile, compileCrepToLoop, loopCompileProg, loopLiveOptimise,
    loopLiveComp, loopShrink, loopShrinkLeaf, loopMarkAll, LoopCall.comp]

end Flapjack
