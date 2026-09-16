import Flapjack.Pipeline
import Flapjack.Parser
import Flapjack.LoopSemantics

/-! Regression tests for the incoming-live fix in crep-to-loop control joins
    (`crep_to_loopScript.sml:176-181,182-188,189-207`): the loop node and the
    call handler cutsets carry the *incoming* live set, not the condition
    expression's own live set.  Narrowing to a smaller set made loop-live
    optimisation drop pre-loop assignments that are still live after the
    loop, changing program results. -/

namespace Flapjack

open Flapjack Parser

def loopLiveRun (source : String) (fuel : Nat) : Option (List Int) :=
  match (parseTopDecs (fun v : Int => BitVec.ofNat 64 v.toNat) source).toOption with
  | none => none
  | some declarations =>
      let result := compileFlapjack (α := BitVec 64) .rv64i 8
          (fun v => BitVec.ofNat 64 v) declarations
      match result.loop with
      | (_, _, body) :: _ =>
          match evalLoopProgWithFunctions result.loop fuel
              { locals := fun _ => none, globals := fun _ => none,
                memory := fun _ => none } body with
          | .some (.returned _ values) => some (values.map (fun v => v.toInt))
          | _ => none
      | [] => none

/- The loop-exit live set must include `out`, keeping the pre-loop assignment
   `out = 7`; before the fix the optimiser dropped it and the program returned
   0. This is an executable regression check. -/
#guard (loopLiveRun
    "\n  fun 1 main () {\n    var 1 out = 7;\n    var 1 i = 0;\n    while i < 2 {\n      i = i + 1;\n    }\n    return out;\n  }\n" 200 ==
    some [7])

/- A wide constant survives the loop-live optimiser unchanged. This is an
   executable regression check. -/
#guard (loopLiveRun
    "\n  fun 1 main () {\n    var 1 x = 1073741832;\n    return x;\n  }\n" 200 ==
    some [1073741832])

end Flapjack
