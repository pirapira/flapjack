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

def runChecks : IO Bool := do
  let expected : Option (List (List Nat)) := some [[], [2, 4], [2, 4]]
  if p1WordVariableNames == expected then
    IO.println "PASS loop_to_word p1 boundary uses dense even Word names"
    pure true
  else
    IO.println s!"FAIL loop_to_word p1 boundary: expected {expected}, got {p1WordVariableNames}"
    pure false

#guard p1WordVariableNames == some [[], [2, 4], [2, 4]]

end Flapjack.Test.LoopToWordBoundaryParity

/-! Oracle tests for the dense-even Word naming boundary at the allocator.
    The original `loop_to_word` `comp_func` computes the assigned variable
    set, removes parameters, and assigns consecutive even Word names via
    `make_ctxt 2 (params ++ variables)`.  These tests pin that boundary on
    the `p1` fixture used by the frame-occupancy oracles. -/
