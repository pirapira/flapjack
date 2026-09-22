import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.LoopLive

namespace Flapjack

/-! The optimised Crepe-to-Loop entry point corresponding to
    `crep_to_loop$ocompile` (`crep_to_loopScript.sml:216`). -/
def oCompile [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) (program : CrepProg α) :
    LoopProg α :=
  loopLiveOptimise (compileCrepToLoop context live program)

/-! Source-named port of CakeML Pancake's `comp_func_def`
    (`crep_to_loopScript.sml:235`).  This keeps the source compiler's
    `make_vmap`/`vmax`/initial-live construction together with `oCompile`,
    rather than duplicating those choices in a pipeline entry point. -/
def crepCompFunc [OfNat α 0] [OfNat α 1]
    (target : RiscV.Architecture) (functions : InfoMap (Nat × Nat))
    (params : List Nat) (body : CrepProg α) : LoopProg α :=
  let context : LoopContext α := crepMkCtxt target (crepMakeVmap params)
    functions (params.length - 1)
  oCompile context (List.range params.length) body

theorem oCompile_skip [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) :
    oCompile context live (.skip : CrepProg α) = .mark .skip := by
  simp [oCompile, compileCrepToLoop, loopCompileProg, loopLiveOptimise,
    loopLiveComp, loopShrink, loopShrinkLeaf, loopMarkAll, LoopCall.comp]

end Flapjack
