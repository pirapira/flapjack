import Flapjack.Parser
import Flapjack.Parser.ParseTopDecsByteRanged
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pipeline
import Flapjack.Pancake.LoopToWord
import Flapjack.RiscV.Allocator

namespace Flapjack.Test.LoopToWordBoundaryParity

open Flapjack Flapjack.LoopToWord

/-- `p1` fixture: identity plus a main with one dead call result. -/
def p1Source : String :=
  "fun 1 id (1 x) { return x; }
fun 1 main() { var 1 t = id(5); return 1; }"

/- `p9` is the smallest accepted struct witness with two distinct values live
   across two calls.  Cake's loop-to-word output has call cutsets `[0]` for
   `mks` and `[0,4,8]` for the later `id` call after dense renaming. -/
def p9Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun S mks (1 a, 1 b) { return S <f = a, g = b>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1,2); var 1 t = id(5); " ++
      "return s.f + s.g; }"

/-- Compile `p1` to its source-shaped loop-level functions, then lower each
    function through the source-facing pipeline boundary. -/
def p1WordBoundaries :
    Option (List (Nat × List Nat × WordProg (RiscV.Word 64))) :=
  match hparse : Parser.parseTopDecs (BitVec.ofInt 64) p1Source with
  | Except.error _ => none
  | Except.ok declarations =>
      let hparsed := Parser.parseTopDecs_declByteRanged
        (BitVec.ofInt 64) p1Source false declarations hparse
      let htarget := panTargetDeclarationsWithDefaultMain_byteRanged declarations hparsed
      (compileFlapjackEntryCake .rv64i (BitVec.ofNat 64 8)
        (fun value => BitVec.ofNat 64 value) "main"
        (panTargetDeclarationsWithDefaultMain declarations) (some (.isTrue htarget))).map
        (fun pipeline => pipelineWordFunctionsSource pipeline.loop)

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

def p9WordBoundaries :
    Option (List (Nat × List Nat × WordProg (RiscV.Word 64))) :=
  match hparse : Parser.parseTopDecs (BitVec.ofInt 64) p9Source with
  | Except.error _ => none
  | Except.ok declarations =>
      let hparsed := Parser.parseTopDecs_declByteRanged
        (BitVec.ofInt 64) p9Source false declarations hparse
      let htarget := panTargetDeclarationsWithDefaultMain_byteRanged declarations hparsed
      (compileFlapjackEntryCake .rv64i (BitVec.ofNat 64 8)
        (fun value => BitVec.ofNat 64 value) "main"
        (panTargetDeclarationsWithDefaultMain declarations) (some (.isTrue htarget))).map
        (fun pipeline => pipelineWordFunctionsSource pipeline.loop)

def p9CallCutsets : Option (List (List (List Nat))) :=
  p9WordBoundaries.map (fun functions =>
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
#guard p9CallCutsets == some [[], [[0], [0, 4, 8]], [], []]

/- Direct `mk_new_cutset` namespace equation: the checked Cake probe
   `comp_call_live` maps source `3` to Word `6`, then inserts link register 0.
   The same constructor is used by production call and FFI lowering. -/
def callCutsetNamespaceOracle : Bool :=
  wordMkNewCutset ({ vars := [(3, 6)] } : WordContext) [3] == [0, 6] &&
    wordMkNewCutset ({ vars := [(3, 6)] } : WordContext) [] == [0]

#guard callCutsetNamespaceOracle

/- The source-facing entry path must use Cake's `comp_func` context and its
   `oCompile` loop-live pass, rather than the legacy pass-local context. -/
def p1EntryUsesSourceLoop : Bool :=
  match hparse : Parser.parseTopDecs (BitVec.ofInt 64) p1Source with
  | Except.error _ => false
  | Except.ok declarations =>
      let hparsed := Parser.parseTopDecs_declByteRanged
        (BitVec.ofInt 64) p1Source false declarations hparse
      let htarget := panTargetDeclarationsWithDefaultMain_byteRanged declarations hparsed
      match compileFlapjackEntryCake .rv64i (BitVec.ofNat 64 8)
          (fun value => BitVec.ofNat 64 value) "main"
          (panTargetDeclarationsWithDefaultMain declarations) (some (.isTrue htarget)) with
      | none => false
      | some pipeline =>
          pipeline.loop.map (fun (_, parameters, _) => parameters) ==
            (pipelineLoopFunctionsSource .rv64i 1 pipeline.crepe).map
              (fun (_, parameters, _) => parameters)

#guard p1EntryUsesSourceLoop

def sourceFunctionParameters : List (Nat × List Nat × LoopProg Nat) :=
  pipelineLoopFunctionsSource .rv64i 64
    [{ name := "f", params := [10, 20], body := (.skip : CrepProg Nat),
       returnShape := .one }]

def sourceCompileProgParameterShape : Bool :=
  match sourceFunctionParameters with
  | [(64, [0, 1], _)] => true
  | _ => false

#guard sourceCompileProgParameterShape

/-! `make_vmap_def` oracle: parameter names receive their dense positional
    slots and no entries are invented for an empty list.  Cake's `FEMPTY |++`
    is a left fold, so the executed list-backed map replays the pairs
    most-recent-first (reversed); lookups are unchanged. -/
def sourceMakeVmapOracle : Bool :=
  crepMakeVmap [] == [] &&
  crepMakeVmap [10, 20, 30] == [(30, 2), (20, 1), (10, 0)] &&
  lookupNatInfo 10 (crepMakeVmap [10, 20, 30]) == some 0 &&
  lookupNatInfo 30 (crepMakeVmap [10, 20, 30]) == some 2

#guard sourceMakeVmapOracle

/-! `comp_func_def` must resolve a source parameter through `make_vmap` before
    lowering.  This representative assignment is the source-to-Loop oracle:
    Cake's parameter name `10` is compiled to dense local slot `0`. -/
def sourceCompFuncOracle : Bool :=
  match crepCompFunc .rv64i [] [10] (.return [.var 10] : CrepProg Nat) with
  | .mark (.seq (.mark (.assign 1 (.var 0))) _) => true
  | _ => false

#guard sourceCompFuncOracle

/-! Cake's `first_name` is 64 and `make_funcs` assigns consecutive labels and
    parameter lengths.  The runtime-facing variant below uses the same
    equation at its reserved label base. -/
def sourceMakeFuncsOracle : Bool :=
  crepFirstName == 64 &&
  match crepMakeFuncs
      [{ name := "f", params := [10, 20], body := (.skip : CrepProg Nat),
         returnShape := .one }] with
  | [("f", (64, 2))] => true
  | _ => false

#guard sourceMakeFuncsOracle

def sourceMakeFuncsSequenceOracle : Bool :=
  match crepMakeFuncs
      [{ name := "f", params := [10, 20], body := (.skip : CrepProg Nat),
         returnShape := .one },
       { name := "g", params := [], body := (.skip : CrepProg Nat),
         returnShape := .one }] with
  | [("f", (64, 2)), ("g", (65, 0))] => true
  | _ => false

#guard sourceMakeFuncsSequenceOracle

/-! `mk_ctxt_def` field-order oracle: the constructor preserves both the
    source-name lookup map and Cake's fresh-variable bound. -/
def sourceMkCtxtOracle : Bool :=
  let context := crepMkCtxt (α := Nat) .rv64i (crepMakeVmap [10, 20])
    [("f", (64, 2))] 1
  context.vars == [(20, 1), (10, 0)] &&
    findLoopVar context 20 == 1 && context.maxVar == 1 &&
    context.functions == [("f", (64, 2))] &&
    match context.target with
    | .rv64i => true
    | _ => false

#guard sourceMkCtxtOracle

/-! Cake's handled-call branch starts handler and return-body labels at the
    next local label and advances once more after both bodies.  This guard
    keeps the source-shaped label state visible independently of final bytes. -/
def handledCallLabelShape : Bool :=
  match loopToWordProgWithLabels ({ vars := [] } : WordContext) (66, 2)
      (.call (some ([7], [8])) (some 11) [2]
        (some (9, .assign 8 (.const 1), .assign 7 (.const 2), []))) with
  | (.seq
      (.call (some ([7], ([0, 8], []), .assign 7 (.const 2), 66, 2))
        (some 11) [2]
        (some (9, .assign 8 (.const 1), 66, 3)))
      .tick, (66, 4)) => true
  | _ => false

#guard handledCallLabelShape

end Flapjack.Test.LoopToWordBoundaryParity

/-! Oracle tests for the dense-even Word naming boundary at the allocator.
    The original `loop_to_word` `comp_func` computes the assigned variable
    set, removes parameters, and assigns consecutive even Word names via
    `make_ctxt 2 (params ++ variables)`.  These tests pin that boundary on
    the `p1` fixture used by the frame-occupancy oracles. -/
