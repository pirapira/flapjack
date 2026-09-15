import Flapjack.Parser
import Flapjack.Compile
import Flapjack.Pipeline
import Flapjack.LoopToWord
import Flapjack.RiscV.Allocator

namespace Flapjack.Test.LoopToWordBoundaryParity

open Flapjack Flapjack.LoopToWord

/-- `p1` fixture: identity plus a main with one dead call result. -/
def p1Source : String :=
  "fun 1 id (1 x) { return x; }
fun 1 main() { var 1 t = id(5); return 1; }"

/-- Compile `p1` to its loop-level functions the way the RISC-V runtime
    image pipeline does, then lower each function through the faithful
    `loopToWordCompFunc` boundary. -/
def p1WordBoundaries :
    Option (List (Nat × List Nat × WordProg (RiscV.Word 64))) := do
  let declarations ← match Parser.parseTopDecs (BitVec.ofInt 64) p1Source with
    | Except.ok declarations => some declarations | Except.error _ => none
  let pipeline ← compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
      (fun value => BitVec.ofNat 64 value) "main"
      (panTargetDeclarationsWithDefaultMain declarations)
  let functions := pipelineLoopFunctions .rv64i stackFunctionFirstLabel
      pipeline.crepe
  some (functions.map (fun (label, parameters, body) =>
    (label, parameters, wordProgDCE (loopToWordCompFunc label parameters body))))

/-- The Word-space names of every lowered `p1` function. -/
def p1WordVariableNames : Option (List (List Nat)) :=
  p1WordBoundaries.map (fun functions =>
    functions.map (fun (_, _, body) =>
      (wordProgVariables body).eraseDups.mergeSort (fun a b => a < b)))

/-- Collect the normal cut set of every call in a lowered Word program. -/
partial def collectCallCutsets (program : WordProg (RiscV.Word 64)) :
    List (List Nat) :=
  match program with
  | .call (some (_, (live, _), _, _, _)) _ _ _ =>
      live :: (programChildren program).flatMap collectCallCutsets
  | .call none _ _ handler =>
      (handler.toList.map (fun (_, body, _, _) => body)).flatMap
        collectCallCutsets
  | _ => (programChildren program).flatMap collectCallCutsets
where
  programChildren : WordProg (RiscV.Word 64) → List (WordProg (RiscV.Word 64))
    | .seq first second => [first, second]
    | .ite _ _ _ thenBranch elseBranch => [thenBranch, elseBranch]
    | .loop _ body _ => [body]
    | .mustTerminate body => [body]
    | .call (some (_, _, returnHandler, _, _)) _ _ exceptionHandler =>
        returnHandler :: (exceptionHandler.toList.map (·.2.1))
    | _ => []

/-- The call cut sets of every lowered `p1` function.  The original
    `loop_to_word` `comp` builds call cut sets with `mk_new_cutset`,
    which always retains register zero. -/
def p1CallCutsets : Option (List (List (List Nat))) :=
  p1WordBoundaries.map (fun functions =>
    functions.map (fun (_, _, body) =>
      (collectCallCutsets body).map
        (fun live => live.mergeSort (fun a b => a < b))))

def runChecks : IO Bool := do
  let expected : Option (List (List Nat)) := some [[0], [0, 2, 4], [0, 2, 4]]
  let cutsetsExpected : Option (List (List (List Nat))) :=
    some [[], [[0]], []]
  let ok₁ := p1WordVariableNames == expected
  let ok₂ := p1CallCutsets == cutsetsExpected
  if ok₁ then
    IO.println "PASS loop_to_word p1 boundary uses dense even Word names"
  else
    IO.println s!"FAIL loop_to_word p1 boundary: expected {expected}, got {p1WordVariableNames}"
  if ok₂ then
    IO.println "PASS loop_to_word p1 call cut sets retain register zero"
  else
    IO.println s!"FAIL loop_to_word p1 call cut sets: expected {cutsetsExpected}, got {p1CallCutsets}"
  pure (ok₁ && ok₂)

#guard p1WordVariableNames == some [[0], [0, 2, 4], [0, 2, 4]]
#guard p1CallCutsets == some [[], [[0]], []]

end Flapjack.Test.LoopToWordBoundaryParity

/-! Oracle tests for the dense-even Word naming boundary at the allocator.
    The original `loop_to_word` `comp_func` computes the assigned variable
    set, removes parameters, and assigns consecutive even Word names via
    `make_ctxt 2 (params ++ variables)`.  These tests pin that boundary on
    the `p1` fixture used by the frame-occupancy oracles. -/
