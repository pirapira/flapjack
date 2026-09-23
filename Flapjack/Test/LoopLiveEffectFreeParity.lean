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
`Load32`, `LoadByte`, `Store32`, `StoreByte`, `ShMem`, or `Ffi` nodes and no
`.call`, so the corresponding `LoopEvaluateHooks` fields are never invoked.
The operations without a faithful Lean port yet (`loop_primop`, `sh_mem_op`,
and the ExtCall `call_FFI` boundary, beads `flapjack-s6a.3.1/.2/.3`) are
supplied as total functions that yield `Error`; `arith` and `setGlobal` are
no-ops.  The successful `[7]` result therefore also witnesses that the
execution path never reaches them.  `effectFree` asserts this structurally
over the compiled `LoopProg`, rejecting every `.call`.  The `eval` hook is a
word-only fixture bridge (`machineToLoopState` drops `.loc` locals/memory); it
is not a faithful general `loopSem$eval` adapter and is not exposed as
production code.  This test does NOT claim `s6a.3` complete.

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
    are never invoked.  A `.call` is accepted only when its direct target
    resolves in the code table to an effect-free body (recursively, with a
    visited set for cycles) and its handler bodies are effect-free; indirect
    calls (`target = none`) are rejected because the callee cannot be checked. -/
partial def effectFreeIn (code : LoopCode Word) (visited : List Nat) :
    LoopProg Word → Bool
  | .primitive .. | .arith .. | .store .. | .setGlobal .. | .load32 ..
  | .loadByte .. | .store32 .. | .storeByte .. | .shMem .. | .ffi .. => false
  | .seq first second => effectFreeIn code visited first && effectFreeIn code visited second
  | .ite _ _ _ thenBranch elseBranch _ =>
      effectFreeIn code visited thenBranch && effectFreeIn code visited elseBranch
  | .loop _ body _ => effectFreeIn code visited body
  | .mark body => effectFreeIn code visited body
  | .call _ target _ handler =>
      let calleeOk :=
        match target with
        | none => false
        | some label =>
            if visited.contains label then true
            else match lookupLoopFunction label code with
              | none => true
              | some (_, body) => effectFreeIn code (label :: visited) body
      let handlerOk :=
        match handler with
        | none => true
        | some (_, body, exceptionHandler, _) =>
            effectFreeIn code visited body &&
              effectFreeIn code visited exceptionHandler
      calleeOk && handlerOk
  | _ => true

/-- Effect-free check for a whole compiled function table plus entry body. -/
def effectFree (code : LoopCode Word) (body : LoopProg Word) : Bool :=
  effectFreeIn code [] body

/-- Word-only fixture bridge from the machine state into the source-shaped
    `LoopState` used by the reviewed `evalLoopExpSource` expression evaluator.

    This is NOT a faithful general `loopSem$eval` adapter and is not exposed as
    production code: a `.loc`-valued local or memory cell is dropped to `none`
    (only `.word` payloads survive).  A path that read a location-valued
    local/memory would therefore evaluate to `none`, fail the machine step, and
    could not produce the asserted successful `[7]` result; the exact-result
    guards below rule out such a path for these fixtures.  `globals` keeps the
    location constructor because `evalLoopExpSource` handles `.loc` there. -/
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

/-- Word-only fixture `eval` hook: `evalLoopExpSource` over the bridged state,
    wrapped back into a `Word` cell as in `loopSem$eval`.  Because
    `machineToLoopState` drops `.loc` locals/memory, this is a fixture adapter
    for word-valued programs only, not a faithful general `loopSem$eval`. -/
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

/-- Hooks for the effect-free fragment.  `primitive`, `store`, `load32`,
    `loadByte`, `store32`, `storeByte`, `shMem`, and `ffi` are deliberately
    total fallbacks that yield `Error`; `arith` and `setGlobal` are no-ops that
    return the state unchanged.  The programs under test never invoke any of
    these fields (see `effectFree`). -/
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

/-- The compiled function table and first (`main`) body of a fixture, for the
    structural check. -/
def mainBodies (source : String) : Option (LoopCode Word × LoopProg Word) :=
  match Parser.parseTopDecs (BitVec.ofInt 64) source with
  | Except.error _ => none
  | Except.ok declarations =>
      match compileFlapjackEntryCake .rv64i (BitVec.ofNat 64 8)
          (fun value => BitVec.ofNat 64 value) "main"
          (panTargetDeclarationsWithDefaultMain declarations) with
      | none => none
      | some pipeline => match pipeline.loop with
          | (_, _, body) :: _ => some (pipeline.loop, body)
          | [] => none

def effectFreeProgram (source : String) : Bool :=
  match mainBodies source with
  | some (code, body) => effectFree code body
  | none => false

def outSevenResult : Option (List Int) := loopRun outSevenSource
def wideConstantResult : Option (List Int) := loopRun wideConstantSource

def outSevenEffectFree : Bool := effectFreeProgram outSevenSource
def wideConstantEffectFree : Bool := effectFreeProgram wideConstantSource

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
