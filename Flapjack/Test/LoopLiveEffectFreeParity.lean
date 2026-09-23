import Flapjack.Parser
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pipeline
import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.LoopSemantics

/-!
# Effect-free `loop_live` regression on the production compiler path

This restores the executable `out = 7` while-loop regression (formerly
`LoopLivePreloopLocals.lean`, removed with the retired `compileFlapjack`
wrapper) on the current production entrypoint `compileFlapjackEntryCake`.

Scope: the test exercises only the *effect-free* fragment of the Loop machine.
The tested programs contain no `Primitive`, `Arith`, `Store`, `SetGlobal`,
`Load32`, `LoadByte`, `Store32`, `StoreByte`, `ShMem`, or `Ffi` nodes, so the
corresponding `LoopEvaluateHooks` fields are never invoked.  The three
operations without a faithful Lean port yet (`loop_primop`, `sh_mem_op`, and
the ExtCall `call_FFI` boundary, beads `flapjack-s6a.3.1/.2/.3`) are supplied
as total functions that yield `Error`; the successful `[7]` result therefore
also witnesses that the execution path never reaches them.  `effectFree`
asserts this structurally over the compiled `LoopProg`.  This test does NOT
claim `s6a.3` complete and does not provide a production adapter.

The reference is the HOL loop-live regression: with the incoming live set at
the loop cutset, the pre-loop assignment `out = 7` stays live and the program
returns 7.
-/

namespace Flapjack.Test.LoopLiveEffectFreeParity

open Flapjack Parser

abbrev Word := RiscV.Word 64

def outSevenSource : String :=
  "\n  fun 1 main () {\n    var 1 out = 7;\n    var 1 i = 0;\n    while i < 2 {\n      i = i + 1;\n    }\n    return out;\n  }\n"

def wideConstantSource : String :=
  "\n  fun 1 main () {\n    var 1 x = 1073741832;\n    return x;\n  }\n"

/-- Structural witness that a compiled program stays in the effect-free
    fragment, so the unported hooks (`primitive`, `arith`, `store`,
    `setGlobal`, `load32`, `loadByte`, `store32`, `storeByte`, `shMem`, `ffi`)
    are never invoked. -/
partial def effectFree : LoopProg Word → Bool
  | .primitive .. | .arith .. | .store .. | .setGlobal .. | .load32 ..
  | .loadByte .. | .store32 .. | .storeByte .. | .shMem .. | .ffi .. => false
  | .seq first second => effectFree first && effectFree second
  | .ite _ _ _ thenBranch elseBranch _ =>
      effectFree thenBranch && effectFree elseBranch
  | .loop _ body _ => effectFree body
  | .mark body => effectFree body
  | .call _ _ _ handler => match handler with
      | some (_, body, exceptionHandler, _) =>
          effectFree body && effectFree exceptionHandler
      | none => true
  | _ => true

/-- Bridge the machine state into the source-shaped `LoopState` used by the
    reviewed `evalLoopExpSource` expression evaluator. -/
def machineToLoopState (state : LoopMachineState Word F) : LoopState Word :=
  { locals := fun name =>
      (state.locals name).bind fun value => match value with
        | .word word => some word
        | .loc _ _ => none
    globals := fun address =>
      (state.globals address).map fun value => match value with
        | .word word => .word word
        | .loc identifier offset => .loc identifier offset
    memory := fun address =>
      (state.memory address).bind fun value => match value with
        | .word word => some word
        | .loc _ _ => none }

/-- Faithful `eval` hook: `evalLoopExpSource` over the bridged state, wrapped
    back into a `Word` cell as in `loopSem$eval`. -/
def evalHook (state : LoopMachineState Word F) (expression : LoopExp Word) :
    Option (LoopValue Word) :=
  (evalLoopExpSource (machineToLoopState state) state.baseAddr state.topAddr
    expression).map .word

/-- Faithful `compare` hook: `word_cmp` via the reviewed `evalLoopCondition`. -/
def compareHook (operator : Cmp) (left right : LoopValue Word) : Bool :=
  match left, right with
  | .word leftWord, .word rightWord =>
      (evalLoopCondition operator leftWord rightWord).getD false
  | _, _ => false

/-- Hooks for the effect-free fragment.  `primitive`, `arith`, `store`,
    `setGlobal`, `load32`, `loadByte`, `store32`, `storeByte`, `shMem`, and
    `ffi` are deliberately total fallbacks that return `Error`; the programs
    under test never invoke them (see `effectFree`). -/
def effectFreeHooks : LoopEvaluateHooks Word Unit where
  eval := evalHook
  primitive := fun _ _ => none
  arith := fun state _ => some state
  store := fun _ _ _ => none
  setGlobal := fun state _ _ => state
  load32 := fun _ _ => none
  loadByte := fun _ _ => none
  store32 := fun _ _ _ => none
  storeByte := fun _ _ _ => none
  compare := compareHook
  shMem := fun _ _ _ state => (some .error, state)
  ffi := fun _ _ _ _ _ _ state => (some .error, state)

def initialState (code : LoopCode Word) : LoopMachineState Word Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none
    mdomain := fun _ => false
    shMdomain := fun _ => false
    clock := 200
    code := code
    be := false
    ffi := trivialFfiState Unit ()
    baseAddr := 0
    topAddr := 0 }

/-- Compile `source` through the production entrypoint and run the first Loop
    function body on the faithful machine. -/
def loopRun (source : String) : Option (List Int) :=
  match Parser.parseTopDecs (BitVec.ofInt 64) source with
  | Except.error _ => none
  | Except.ok declarations =>
      match compileFlapjackEntryCake .rv64i (BitVec.ofNat 64 8)
          (fun value => BitVec.ofNat 64 value) "main"
          (panTargetDeclarationsWithDefaultMain declarations) with
      | none => none
      | some pipeline =>
          match pipeline.loop with
          | (_, _, body) :: _ =>
              match evaluateLoop 200 effectFreeHooks body
                  (initialState pipeline.loop) with
              | (some (.result values), _) =>
                  some (values.map fun value => match value with
                    | .word word => word.toInt
                    | .loc _ _ => 0)
              | _ => none
          | [] => none

/-- The compiled `main` bodies of both fixtures, for the structural check. -/
def mainBodies (source : String) : Option (LoopProg Word) :=
  match Parser.parseTopDecs (BitVec.ofInt 64) source with
  | Except.error _ => none
  | Except.ok declarations =>
      match compileFlapjackEntryCake .rv64i (BitVec.ofNat 64 8)
          (fun value => BitVec.ofNat 64 value) "main"
          (panTargetDeclarationsWithDefaultMain declarations) with
      | none => none
      | some pipeline => match pipeline.loop with
          | (_, _, body) :: _ => some body
          | [] => none

def outSevenResult : Option (List Int) := loopRun outSevenSource
def wideConstantResult : Option (List Int) := loopRun wideConstantSource

def outSevenEffectFree : Bool :=
  (mainBodies outSevenSource).any effectFree
def wideConstantEffectFree : Bool :=
  (mainBodies wideConstantSource).any effectFree

def outSevenMatches : Bool := outSevenResult == some [7]
def wideConstantMatches : Bool := wideConstantResult == some [1073741832]

#guard outSevenEffectFree
#guard wideConstantEffectFree
#guard outSevenMatches
#guard wideConstantMatches

def runChecks : IO Bool := do
  let checks :=
    [ ("Loop effect-free out=7 loop_live regression is effect-free",
        outSevenEffectFree),
      ("Loop effect-free out=7 loop_live regression returns 7",
        outSevenMatches),
      ("Loop effect-free wide-constant regression is effect-free",
        wideConstantEffectFree),
      ("Loop effect-free wide-constant regression returns the constant",
        wideConstantMatches) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopLiveEffectFreeParity
