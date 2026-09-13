import Flapjack.LoopStateResult
import Flapjack.LoopCallEnv
import Flapjack.LoopFindCode
import Flapjack.LoopGetVarImm
import Flapjack.LoopSetVars

/-!
# Pancake `loopSem.evaluate`

This is the equation-level port of
`cakeml/pancake/semantics/loopSemScript.sml:278` (`evaluate_def`).  The
machine-state boundary deliberately keeps the source's effectful operations
as hooks: expression evaluation, arithmetic, ordinary memory, shared memory,
and FFI each have their own already-tested source-shaped port.  The recursive
control machine below is therefore the direct `evaluate_def` composition of
those operations, rather than a second approximation of their internals.

The executable probe uses the `LoopWordLoc` specialization.  This is the same
word/location representation used by `LoopMachineState` and `findLoopCode`.
-/

namespace Flapjack

abbrev LoopMachineStep :=
  Option (LoopMachineResult LoopWordLoc) × LoopMachineState LoopWordLoc

structure LoopEvaluateHooks where
  eval : LoopMachineState LoopWordLoc → LoopExp LoopWordLoc → Option LoopWordLoc
  primitive : PrimOp → List LoopWordLoc → Option (List LoopWordLoc)
  arith : LoopMachineState LoopWordLoc → LoopArith →
    Option (LoopMachineState LoopWordLoc)
  store : LoopMachineState LoopWordLoc → LoopWordLoc → LoopWordLoc →
    Option (LoopMachineState LoopWordLoc)
  setGlobal : LoopMachineState LoopWordLoc → LoopWordLoc → LoopWordLoc →
    LoopMachineState LoopWordLoc
  load32 : LoopMachineState LoopWordLoc → LoopWordLoc → Option LoopWordLoc
  loadByte : LoopMachineState LoopWordLoc → LoopWordLoc → Option LoopWordLoc
  store32 : LoopMachineState LoopWordLoc → LoopWordLoc → LoopWordLoc →
    Option (LoopMachineState LoopWordLoc)
  storeByte : LoopMachineState LoopWordLoc → LoopWordLoc → LoopWordLoc →
    Option (LoopMachineState LoopWordLoc)
  compare : Cmp → LoopWordLoc → LoopWordLoc → Bool
  shMem : CrepMemOp → Nat → LoopWordLoc → LoopMachineState LoopWordLoc →
    LoopMachineStep
  ffi : FunName → Nat → Nat → Nat → Nat → List Nat →
    LoopMachineState LoopWordLoc → LoopMachineStep

def loopMachineGetVars (locals : Nat → Option LoopWordLoc) :
    List Nat → Option (List LoopWordLoc)
  | [] => some []
  | name :: names => do
      let value ← locals name
      let values ← loopMachineGetVars locals names
      pure (value :: values)

def loopMachineSetVars (state : LoopMachineState LoopWordLoc)
    (names : List Nat) (values : List LoopWordLoc) :
    LoopMachineState LoopWordLoc :=
  { state with locals := loopSetVars state.locals names values }

def fixLoopMachineClock (oldState : LoopMachineState LoopWordLoc)
    (step : LoopMachineStep) : LoopMachineStep :=
  let (result, newState) := step
  (result, { newState with
    clock := if oldState.clock < newState.clock then oldState.clock
      else newState.clock })

def loopIsLoad : CrepMemOp → Bool
  | .load | .load8 | .load16 | .load32 => true
  | .store | .store8 | .store16 | .store32 => false

def loopSetGlobalMachine (state : LoopMachineState LoopWordLoc)
    (address value : LoopWordLoc) : LoopMachineState LoopWordLoc :=
  match address with
  | .word address =>
      { state with globals := fun current =>
          if current == address then some value else state.globals current }
  | .loc _ _ => state

mutual
  def evaluateLoop : Nat → LoopEvaluateHooks → LoopProg LoopWordLoc →
      LoopMachineState LoopWordLoc → LoopMachineStep
    | 0, _, _, state => (some .error, state)
    | fuel + 1, hooks, program, state => match program with
    | .skip => (none, state)
    | .fail => (some .error, state)
    | .assign name expression =>
        match hooks.eval state expression with
        | none => (some .error, state)
        | some value =>
            (none, { state with locals := loopSetVar state.locals name value })
    | .primitive destinations operator arguments =>
        match loopMachineGetVars state.locals arguments with
        | none => (some .error, state)
        | some values =>
            match hooks.primitive operator values with
            | none => (some .error, state)
            | some resultValues =>
                if destinations.length = resultValues.length then
                  (none, loopMachineSetVars state destinations resultValues)
                else (some .error, state)
    | .arith operation =>
        match hooks.arith state operation with
        | none => (some .error, state)
        | some newState => (none, newState)
    | .store address value =>
        match hooks.eval state address, state.locals value with
        | some addressValue, some sourceValue =>
            match addressValue with
            | .word _ =>
              match hooks.store state addressValue sourceValue with
              | some newState => (none, newState)
              | none => (some .error, state)
            | .loc _ _ => (some .error, state)
        | _, _ => (some .error, state)
    | .setGlobal address expression =>
        match hooks.eval state expression with
        | some value => (none, hooks.setGlobal state address value)
        | none => (some .error, state)
    | .load32 address destination =>
        match state.locals address with
        | some addressValue =>
            match addressValue with
            | .word _ =>
              match hooks.load32 state addressValue with
              | some value => (none, { state with locals := loopSetVar state.locals destination value })
              | none => (some .error, state)
            | .loc _ _ => (some .error, state)
        | _ => (some .error, state)
    | .loadByte address destination =>
        match state.locals address with
        | some addressValue =>
            match addressValue with
            | .word _ =>
              match hooks.loadByte state addressValue with
              | some value => (none, { state with locals := loopSetVar state.locals destination value })
              | none => (some .error, state)
            | .loc _ _ => (some .error, state)
        | _ => (some .error, state)
    | .store32 address value =>
        match state.locals address, state.locals value with
        | some addressValue, some valueValue =>
            match addressValue, valueValue with
            | .word _, .word _ =>
              match hooks.store32 state addressValue valueValue with
              | some newState => (none, newState)
              | none => (some .error, state)
            | _, _ => (some .error, state)
        | _, _ => (some .error, state)
    | .storeByte address value =>
        match state.locals address, state.locals value with
        | some addressValue, some valueValue =>
            match addressValue, valueValue with
            | .word _, .word _ =>
              match hooks.storeByte state addressValue valueValue with
              | some newState => (none, newState)
              | none => (some .error, state)
            | _, _ => (some .error, state)
        | _, _ => (some .error, state)
    | .seq first second =>
        let (result, state') := fixLoopMachineClock state (evaluateLoop fuel hooks first state)
        if result.isNone then evaluateLoop fuel hooks second state' else (result, state')
    | .ite operator condition right thenBranch elseBranch live =>
        match state.locals condition, getVarImm state right with
        | some left, some rightValue =>
            let branch := if hooks.compare operator left rightValue then thenBranch
              else elseBranch
            cutLoopResult live (evaluateLoop fuel hooks branch state)
        | _, _ => (some .error, state)
    | .mark body => evaluateLoop fuel hooks body state
    | .break label => (some (.break label), state)
    | .continue label => (some (.continue label), state)
    | .loop liveIn body liveOut =>
        match cutLoopResult liveIn (none, state) with
        | (none, state') =>
            match fixLoopMachineClock state' (evaluateLoop fuel hooks body state') with
            | (none, bodyState) => evaluateLoop fuel hooks (.loop liveIn body liveOut) bodyState
            | (some (.continue 0), bodyState) =>
                evaluateLoop fuel hooks (.loop liveIn body liveOut) bodyState
            | (some (.break 0), bodyState) =>
                cutLoopResult liveOut (none, bodyState)
            | (result, bodyState) => (exitLoop result, bodyState)
        | result => result
    | .raise name =>
        match state.locals name with
        | none => (some .error, state)
        | some value => (some (.except value), callEnv [] state)
    | .return names =>
        match loopMachineGetVars state.locals names with
        | some values => (some (.result values), callEnv [] state)
        | none => (some .error, state)
    | .shMem operator name address =>
        match hooks.eval state address with
        | some addressValue =>
            match addressValue with
            | .word _ =>
            if loopIsLoad operator then
              if (state.locals name).isSome then
                hooks.shMem operator name addressValue state
              else (some .error, state)
            else
              match state.locals name with
              | some (.word _) =>
                  hooks.shMem operator name addressValue state
              | _ => (some .error, state)
            | .loc _ _ => (some .error, state)
        | _ => (some .error, state)
    | .tick =>
        if state.clock = 0 then (some .timeOut, { state with locals := fun _ => none })
        else (none, decrementLoopClock state)
    | .locValue destination source =>
        if state.code.any (fun (label, _, _) => label = source) then
          (none, { state with locals := loopSetVar state.locals destination (.loc source 0) })
        else (some .error, state)
    | .call returns target arguments handler =>
        evaluateLoopCall fuel hooks returns target arguments handler state
    | .ffi function configuration configurationLength array arrayLength live =>
        match cutLoopState live state with
        | none => (some .error, state)
        | some state' =>
            hooks.ffi function configuration configurationLength array arrayLength live state'
  termination_by fuel _ _ _ => fuel

  def evaluateLoopCall : Nat → LoopEvaluateHooks →
      Option (List Nat × List Nat) → Option Nat → List Nat →
      Option (Nat × LoopProg LoopWordLoc × LoopProg LoopWordLoc × List Nat) →
      LoopMachineState LoopWordLoc → LoopMachineStep
    | 0, _, _, _, _, _, state => (some .error, state)
    | fuel + 1, hooks, returns, target, arguments, handler, state =>
      match loopMachineGetVars state.locals arguments with
    | none => (some .error, state)
    | some argumentValues =>
        match findLoopCode target argumentValues state.code with
        | none => (some .error, state)
        | some (environment, body) =>
            match returns with
            | none =>
                if handler.isSome then (some .error, state)
                else if state.clock = 0 then
                  (some .timeOut, { state with locals := fun _ => none })
                else
                  match evaluateLoop fuel hooks body
                      { state with locals := environment, clock := state.clock - 1 } with
                  | (some (.continue _), state') | (some (.break _), state') =>
                      (some .error, state')
                  | result => result
            | some (names, live) =>
                if names.eraseDups.length ≠ names.length then (some .error, state)
                else
                  match cutLoopResult live (none, state) with
                  | (none, cutState) =>
                      let bodyState := { cutState with locals := environment }
                      match fixLoopMachineClock bodyState (evaluateLoop fuel hooks body bodyState) with
                      | (some (.result values), finished) =>
                          if values.length ≠ names.length then (some .error, finished)
                          else
                            match handler with
                            | none => (none, loopMachineSetVars
                                { finished with locals := cutState.locals } names values)
                            | some (_, _, handlerBody, liveOut) =>
                                cutLoopResult liveOut
                                  (evaluateLoop fuel hooks handlerBody
                                    (loopMachineSetVars
                                      { finished with locals := cutState.locals } names values))
                      | (some (.except exception), finished) =>
                          match handler with
                          | none => (some (.except exception), callEnv [] finished)
                          | some (name, handlerBody, _, liveOut) =>
                              cutLoopResult liveOut
                                (evaluateLoop fuel hooks handlerBody
                                  { (callEnv [] finished) with locals := loopSetVar cutState.locals name exception })
                      | (some (.continue _), finished) | (some (.break _), finished) =>
                          (some .error, finished)
                      | (none, finished) => (some .error, finished)
                      | result => result
                  | result => result
  termination_by fuel _ _ _ _ _ _ => fuel

end

end Flapjack
