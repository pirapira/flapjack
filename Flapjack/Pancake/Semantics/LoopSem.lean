import Flapjack.LoopStateResult
import Flapjack.LoopCallEnv
import Flapjack.LoopFindCode
import Flapjack.LoopGetVarImm
import Flapjack.LoopSetVars
import Flapjack.LoopArith
import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.Pancake.Semantics.CrepRuntimeTarget

/-!
# Pancake `loopSem.evaluate`

This is the equation-level port of
`cakeml/pancake/semantics/loopSemScript.sml:278` (`evaluate_def`).  The
machine-state boundary deliberately keeps the source's effectful operations
as hooks: expression evaluation, arithmetic, ordinary memory, shared memory,
and FFI each have their own already-tested source-shaped port.  The recursive
control machine below is therefore the direct `evaluate_def` composition of
those operations, rather than a second approximation of their internals.

The executable probe uses the `Nat` word specialization, so machine values are
`LoopValue Nat = LoopWordLoc`; the program and code table carry the raw word
type (`LoopProg W`, `LoopCode W`), exactly as in the source `'a loopLang$prog`.
-/

namespace Flapjack

/-- One step of the loop machine, word-parametric: `W` is the underlying word
    type (the payload of `LoopValue`) and `F` is the oracle host-state type of
    `LoopMachineState.ffi : FfiState F`.  The defaults recover the original
    `Nat`/`LoopWordLoc` specialization used by the executable probe. -/
abbrev LoopMachineStep (W : Type := Nat) (F : Type := LoopWordLoc) :=
  Option (LoopMachineResult W) × LoopMachineState W F

/-- Effectful operations of `loopSem$evaluate`, word-parametric in `W`/`F` so
    the same equation-level machine serves the source probe (`W = Nat`,
    `F = LoopWordLoc`) and the production `BitVec` IR. -/
structure LoopEvaluateHooks (W : Type := Nat) (F : Type := LoopWordLoc) where
  eval : LoopMachineState W F → LoopExp W → Option (LoopValue W)
  primitive : PrimOp → List (LoopValue W) → Option (List (LoopValue W))
  arith : LoopMachineState W F → LoopArith → Option (LoopMachineState W F)
  store : LoopMachineState W F → LoopValue W → LoopValue W →
    Option (LoopMachineState W F)
  setGlobal : LoopMachineState W F → BitVec 5 → LoopValue W →
    LoopMachineState W F
  load32 : LoopMachineState W F → LoopValue W → Option (LoopValue W)
  loadByte : LoopMachineState W F → LoopValue W → Option (LoopValue W)
  store32 : LoopMachineState W F → LoopValue W → LoopValue W →
    Option (LoopMachineState W F)
  storeByte : LoopMachineState W F → LoopValue W → LoopValue W →
    Option (LoopMachineState W F)
  compare : Cmp → LoopValue W → LoopValue W → Bool
  shMem : CrepMemOp → Nat → LoopValue W → LoopMachineState W F →
    LoopMachineStep W F
  ffi : FunName → Nat → Nat → Nat → Nat → List Nat →
    LoopMachineState W F → LoopMachineStep W F

def loopMachineGetVars {W : Type} (locals : Nat → Option (LoopValue W)) :
    List Nat → Option (List (LoopValue W))
  | [] => some []
  | name :: names => do
      let value ← locals name
      let values ← loopMachineGetVars locals names
      pure (value :: values)

def loopMachineSetVars {W F : Type} (state : LoopMachineState W F)
    (names : List Nat) (values : List (LoopValue W)) :
    LoopMachineState W F :=
  { state with locals := loopSetVars state.locals names values }

def fixLoopMachineClock {W F : Type} (oldState : LoopMachineState W F)
    (step : LoopMachineStep W F) : LoopMachineStep W F :=
  let (result, newState) := step
  (result, { newState with
    clock := if oldState.clock < newState.clock then oldState.clock
      else newState.clock })

def loopIsLoad : CrepMemOp → Bool
  | .load | .load8 | .load16 | .load32 => true
  | .store | .store8 | .store16 | .store32 => false

def loopSetGlobalMachine {W F : Type} (state : LoopMachineState W F)
    (address : BitVec 5) (value : LoopValue W) : LoopMachineState W F :=
  { state with globals := fun current =>
      if current == address then some value else state.globals current }

/-! Bridge the source-shaped `loop_arith` port into the exact machine-state
    evaluator.  `loopArith` is defined on `Nat` words, so this helper is the
    `W = Nat` instance; the FFI type stays free.  Non-word locals remain
    untouched, while every word local returned by `loopArith` is written back
    as a `Word`; a missing operand therefore still produces the source `NONE`
    result. -/
def loopArithMachine (width : Nat) (state : LoopMachineState Nat F)
    (operation : LoopArith) : Option (LoopMachineState Nat F) :=
  let locals : Nat → Option Nat := fun name =>
    match state.locals name with
    | some (.word value) => some value
    | some (.loc _ _) | none => none
  match loopArith width operation locals with
  | none => none
  | some updated =>
      some { state with locals := (fun name =>
        match updated name with
        | some value => some (.word value)
        | none => state.locals name) }

mutual
  def evaluateLoop {W F : Type} : Nat → LoopEvaluateHooks W F →
      LoopProg W → LoopMachineState W F → LoopMachineStep W F
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

  def evaluateLoopCall {W F : Type} : Nat → LoopEvaluateHooks W F →
      Option (List Nat × List Nat) → Option Nat → List Nat →
      Option (Nat × LoopProg W × LoopProg W × List Nat) →
      LoopMachineState W F → LoopMachineStep W F
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
                  | (none, state') => (some .error, state')
                  | (some result, state') => (some result, state')
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

/-- HOL `loopSem$loop_primop` (`cakeml/pancake/semantics/loopSemScript.sml:242-252`).
    The only Loop primitive is `AddCarry`: it accepts exactly three word cells
    and returns the low word followed by the carry word; a malformed arity or
    any non-word cell yields `none`.  This is the `LoopEvaluateHooks.primitive`
    boundary over word-location cells. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "loop_primop_def"]
def loopPrimopHOL {width : Nat} [NeZero width] :
    PrimOp → List (LoopValue (BitVec width)) →
      Option (List (LoopValue (BitVec width)))
  | .addCarry, [.word left, .word right, .word carry] =>
      let (result, overflow) := wordAddCarryHOL left right carry
      some [.word result, .word overflow]
  | _, _ => none

/-! Faithful 64-bit instances of CakeML's `sh_mem_load`, `sh_mem_store`, and
    `sh_mem_op` (`cakeml/pancake/semantics/loopSemScript.sml:198-262`).  HOL's
    `word_to_bytes`/`word_of_bytes`/`byte_align` are determined by the word
    type; for the 64-bit machine we use the reviewed RISC-V byte codec
    `riscv64GetByte`/`riscv64PutBytes` and `panRiscVByteAlign`.  These are the
    `LoopEvaluateHooks.shMem` boundary over word-location cells. -/

/-- The source byte-count argument `[n2w nb]` handed to `call_FFI`. -/
def loopShMemByteCount (width : Nat) : List UInt8 := [UInt8.ofNat width]

/-! FLAPJACK-SPECIFIC (not an exact HOL port).  HOL `loopSem$sh_mem_load_def`
    (`loopSemScript.sml:198-215`) is polymorphic in the word type `'a` and uses
    the `word_to_bytes`/`word_of_bytes`/`byte_align` codec; this definition fixes
    `RiscV.Word 64` and the RV64 little-endian codec (`riscv64GetByte` /
    `riscv64PutBytes`).  The zero-width case checks the raw address and omits
    HOL's unreachable FFI fallback; the nonzero case checks `byte_align address`
    and keeps that fallback.  The exact polymorphic port is tracked by
    flapjack-s6a.3.2.1 and recorded as a documented mismatch. -/
def loopShMemLoad (state : LoopMachineState (RiscV.Word 64) F)
    (name : Nat) (address : RiscV.Word 64) (width : Nat) :
    LoopMachineStep (RiscV.Word 64) F :=
  let aligned := if width = 0 then address
    else RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address
  let addressBytes := (List.range 8).map (fun index => riscv64GetByte index address)
  let call := callFfi state.ffi (.sharedMem .mappedRead)
    (loopShMemByteCount width) addressBytes
  if width = 0 then
    if state.shMdomain address then
      match call with
      | .final event => (some (.finalFfi event), callEnv [] state)
      | .returned newFfi bytes =>
          let updated : LoopMachineState (RiscV.Word 64) F :=
            { state with
              ffi := newFfi
              locals := loopSetVar state.locals name
                (.word (riscv64PutBytes false 0 bytes 0)) }
          (none, updated)
    else (some .error, state)
  else
    if state.shMdomain aligned then
      match call with
      | .final event => (some (.finalFfi event), callEnv [] state)
      | .returned newFfi bytes =>
          let updated : LoopMachineState (RiscV.Word 64) F :=
            { state with
              ffi := newFfi
              locals := loopSetVar state.locals name
                (.word (riscv64PutBytes false 0 bytes 0)) }
          (none, updated)
    else (some .error, state)

/-! FLAPJACK-SPECIFIC (not an exact HOL port).  HOL `loopSem$sh_mem_store_def`
    (`loopSemScript.sml:217-243`) is polymorphic in the word type `'a` and uses
    the `word_to_bytes` codec; this definition fixes `RiscV.Word 64` and the RV64
    little-endian codec.  Only a word-valued local can be stored; the payload is
    the value bytes followed by the address bytes (truncated to `width` for
    nonzero widths).  The exact polymorphic port is tracked by the dependency
    bead and recorded as a documented mismatch. -/
def loopShMemStore (state : LoopMachineState (RiscV.Word 64) F)
    (name : Nat) (address : RiscV.Word 64) (width : Nat) :
    LoopMachineStep (RiscV.Word 64) F :=
  match state.locals name with
  | some (.word value) =>
      let aligned := if width = 0 then address
        else RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address
      let valueBytes := (List.range 8).map (fun index => riscv64GetByte index value)
      let addressBytes := (List.range 8).map (fun index => riscv64GetByte index address)
      let payload := if width = 0 then valueBytes ++ addressBytes
        else valueBytes.take width ++ addressBytes
      let call := callFfi state.ffi (.sharedMem .mappedWrite)
        (loopShMemByteCount width) payload
      if width = 0 then
        if state.shMdomain address then
          match call with
          | .final event => (some (.finalFfi event), callEnv [] state)
          | .returned newFfi _ => (none, { state with ffi := newFfi })
        else (some .error, state)
      else
        if state.shMdomain aligned then
          match call with
          | .final event => (some (.finalFfi event), callEnv [] state)
          | .returned newFfi _ => (none, { state with ffi := newFfi })
        else (some .error, state)
  | _ => (some .error, state)

/-! FLAPJACK-SPECIFIC (not an exact HOL port).  HOL `loopSem$sh_mem_op_def`
    (`loopSemScript.sml:255-262`) dispatches over the polymorphic word type; this
    definition fixes `RiscV.Word 64` because it delegates to the specialized
    `loopShMemLoad`/`loopShMemStore`.  The dispatch table itself (width 0, 1, 2,
    or 4) matches HOL.  The exact polymorphic port is tracked by the dependency
    bead and recorded as a documented mismatch. -/
def loopShMemOp (state : LoopMachineState (RiscV.Word 64) F)
    (operator : CrepMemOp) (name : Nat) (address : RiscV.Word 64) :
    LoopMachineStep (RiscV.Word 64) F :=
  match operator with
  | .load => loopShMemLoad state name address 0
  | .store => loopShMemStore state name address 0
  | .load8 => loopShMemLoad state name address 1
  | .store8 => loopShMemStore state name address 1
  | .load16 => loopShMemLoad state name address 2
  | .store16 => loopShMemStore state name address 2
  | .load32 => loopShMemLoad state name address 4
  | .store32 => loopShMemStore state name address 4

/-- The `LoopEvaluateHooks.shMem` boundary: unwrap the evaluated address cell. -/
def loopShMemHook (state : LoopMachineState (RiscV.Word 64) F)
    (operator : CrepMemOp) (name : Nat) : LoopValue (RiscV.Word 64) →
    LoopMachineStep (RiscV.Word 64) F
  | .word address => loopShMemOp state operator name address
  | .loc _ _ => (some .error, state)

/-- Width-generic exact port of HOL `read_bytearray_def` (`miscScript.sml:113`).
    The byte reader is supplied as HOL's own `get_byte` argument, so no extra
    codec parameter is introduced; the word type is a parameter as in HOL. -/
@[hol "cakeml/misc/miscScript.sml" "read_bytearray_def"]
def readBytearrayHOL {width : Nat} (address : RiscV.Word width) (length : Nat)
    (getByte : RiscV.Word width → Option UInt8) : Option (List UInt8) :=
  match length with
  | 0 => some []
  | length + 1 => do
      let byte ← getByte address
      let rest ← readBytearrayHOL (address + 1) length getByte
      pure (byte :: rest)

/-- Width-generic port of HOL `byte$get_byte` (`src/n-bit/byteScript.sml:21`).
    That script is part of the HOL standard library rather than the CakeML
    submodule, so this declaration carries no HOL tag.  The byte shift is
    `8 * (w2n address MOD (dimindex DIV 8))`, reversed for big-endian words. -/
def riscvGetByteHOL {width : Nat} [NeZero width] (bigEndian : Bool)
    (address value : RiscV.Word width) : UInt8 :=
  let bytesInWord := width / 8
  let shift :=
    if bigEndian then 8 * ((bytesInWord - 1) - (address.toNat % bytesInWord))
    else 8 * (address.toNat % bytesInWord)
  UInt8.ofNat ((value >>> shift).toNat % 256)

/-- Width-generic port of HOL `byte$byte_align` (`src/n-bit/alignmentScript.sml:23`):
    `byte_align (w : 'a word) = align (LOG2 (dimindex(:'a) DIV 8)) w`, i.e. the
    low `LOG2 (width DIV 8)` bits of the address are cleared.  That script is
    part of the HOL standard library rather than the CakeML submodule, so this
    declaration carries no HOL tag.  Note that this is *not* division by
    `width / 8`: it agrees with `RiscV.panRiscVByteAlign (width / 8)` only when
    `width / 8` is a power of two (e.g. width 64).  For width 24, HOL clears one
    low bit and aligns by 2, whereas dividing by 3 would align by 3. -/
def riscvByteAlignHOL {width : Nat} [NeZero width] (address : RiscV.Word width) :
    RiscV.Word width :=
  let bits := Nat.log2 (width / 8)
  (address >>> bits) <<< bits

/-- Width-generic exact port of HOL `mem_load_byte_aux_def`
    (`wordSemScript.sml:159`).  As in HOL, `memory` is a total
    `'a word -> 'a word_loc` map (Lean `LoopValue` is the `word_loc`
    counterpart) and `domain` is the address set `dm`; the word type is a
    parameter, so no extra codec parameter is introduced. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_load_byte_aux_def"]
def memLoadByteAuxHOL {width : Nat} [NeZero width]
    (memory : RiscV.Word width → LoopValue (RiscV.Word width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) : Option UInt8 :=
  let aligned := riscvByteAlignHOL address
  match memory aligned with
  | .loc _ _ => none
  | .word value =>
      if domain aligned then some (riscvGetByteHOL bigEndian address value) else none

/-- Width-generic port of HOL `byte$set_byte` (`src/n-bit/byteScript.sml:28`).
    That script is part of the HOL standard library rather than the CakeML
    submodule, so this declaration carries no HOL tag.  It replaces the byte at
    `byte_index address bigEndian` by `byte`. -/
def riscvSetByteHOL {width : Nat} [NeZero width] (bigEndian : Bool)
    (address value : RiscV.Word width) (byte : UInt8) : RiscV.Word width :=
  let bytesInWord := width / 8
  let index :=
    if bigEndian then 8 * ((bytesInWord - 1) - (address.toNat % bytesInWord))
    else 8 * (address.toNat % bytesInWord)
  let mask := ~~~((BitVec.ofNat width 0xFF) <<< index)
  (value &&& mask) ||| ((BitVec.ofNat width byte.toNat) <<< index)

/-- Width-generic exact port of HOL `mem_store_byte_aux_def`
    (`wordSemScript.sml:171`).  As in HOL, `memory` is a total
    `'a word -> 'a word_loc` map and `domain` is the address set `dm`, so no
    extra codec parameter is introduced. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_store_byte_aux_def"]
def memStoreByteAuxHOL {width : Nat} [NeZero width]
    (memory : RiscV.Word width → LoopValue (RiscV.Word width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool)
    (address : RiscV.Word width) (byte : UInt8) :
    Option (RiscV.Word width → LoopValue (RiscV.Word width)) :=
  let aligned := riscvByteAlignHOL address
  match memory aligned with
  | .word value =>
      if domain aligned then
        let updated := riscvSetByteHOL bigEndian address value byte
        some (fun current => if current = aligned then .word updated else memory current)
      else none
  | _ => none

/-- Width-generic exact port of HOL `write_bytearray_def`
    (`wordSemScript.sml:178`).  The argument order matches HOL
    `write_bytearray a bs m dm be`; as in HOL, a failed byte store leaves the
    original memory unchanged. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "write_bytearray_def"]
def writeBytearrayHOL {width : Nat} [NeZero width]
    (address : RiscV.Word width) (bytes : List UInt8)
    (memory : RiscV.Word width → LoopValue (RiscV.Word width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) : RiscV.Word width → LoopValue (RiscV.Word width) :=
  match bytes with
  | [] => memory
  | byte :: rest =>
      match memStoreByteAuxHOL
          (writeBytearrayHOL (address + 1) rest memory domain bigEndian)
          domain bigEndian address byte with
      | some updated => updated
      | none => memory

/-- Width-generic port of HOL `byte$word_to_bytes`
    (`src/n-bit/byteScript.sml:450`):
    `word_to_bytes w be = word_to_bytes_aux (dimindex DIV 8) w be`, i.e. the
    `get_byte` of each increasing index.  That script is part of the HOL
    standard library rather than the CakeML submodule, so this declaration
    carries no HOL tag. -/
def riscvWordToBytesHOL {width : Nat} [NeZero width]
    (value : RiscV.Word width) (bigEndian : Bool) : List UInt8 :=
  (List.range (width / 8)).map
    (fun index => riscvGetByteHOL bigEndian (BitVec.ofNat width index) value)

/-- Width-generic port of HOL `byte$word_of_bytes`
    (`src/n-bit/byteScript.sml:197`): fold `set_byte` over the bytes starting at
    `address` and incrementing by one.  HOL standard library, so no HOL tag. -/
def riscvWordOfBytesHOL {width : Nat} [NeZero width]
    (bigEndian : Bool) (address : RiscV.Word width) :
    List UInt8 → RiscV.Word width
  | [] => 0
  | byte :: rest =>
      riscvSetByteHOL bigEndian address
        (riscvWordOfBytesHOL bigEndian (address + 1) rest) byte

/-- Width-generic exact port of HOL `loopSem$sh_mem_load_def`
    (`loopSemScript.sml:198-215`).  The word codec `word_to_bytes`/`word_of_bytes`
    is supplied generically by `riscvWordToBytesHOL`/`riscvWordOfBytesHOL`, so no
    extra codec parameter is introduced and the word type stays polymorphic.
    HOL's unreachable `_ => (SOME Error, s)` alternative after the two `FFI`
    constructors is omitted because `FfiResult` has exactly those two. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "sh_mem_load_def"]
def shMemLoadHOL {width : Nat} [NeZero width]
    (state : LoopMachineState (RiscV.Word width) F)
    (name : Nat) (address : RiscV.Word width) (byteCount : Nat) :
    LoopMachineStep (RiscV.Word width) F :=
  let addressBytes := riscvWordToBytesHOL address false
  let call := callFfi state.ffi (.sharedMem .mappedRead)
    (loopShMemByteCount byteCount) addressBytes
  if byteCount = 0 then
    if state.shMdomain address then
      match call with
      | .final event => (some (.finalFfi event), callEnv [] state)
      | .returned newFfi bytes =>
          let updated : LoopMachineState (RiscV.Word width) F :=
            { state with
              ffi := newFfi
              locals := loopSetVar state.locals name
                (.word (riscvWordOfBytesHOL false 0 bytes)) }
          (none, updated)
    else (some .error, state)
  else
    if state.shMdomain (riscvByteAlignHOL (width := width) address) then
      match call with
      | .final event => (some (.finalFfi event), callEnv [] state)
      | .returned newFfi bytes =>
          let updated : LoopMachineState (RiscV.Word width) F :=
            { state with
              ffi := newFfi
              locals := loopSetVar state.locals name
                (.word (riscvWordOfBytesHOL false 0 bytes)) }
          (none, updated)
    else (some .error, state)

/-- Width-generic exact port of HOL `loopSem$sh_mem_store_def`
    (`loopSemScript.sml:217-243`).  Only a word-valued local can be stored; the
    payload is the value bytes followed by the address bytes, truncated to
    `byteCount` for nonzero widths. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "sh_mem_store_def"]
def shMemStoreHOL {width : Nat} [NeZero width]
    (state : LoopMachineState (RiscV.Word width) F)
    (name : Nat) (address : RiscV.Word width) (byteCount : Nat) :
    LoopMachineStep (RiscV.Word width) F :=
  match state.locals name with
  | some (.word value) =>
      let valueBytes := riscvWordToBytesHOL value false
      let addressBytes := riscvWordToBytesHOL address false
      if byteCount = 0 then
        if state.shMdomain address then
          match callFfi state.ffi (.sharedMem .mappedWrite)
              (loopShMemByteCount byteCount)
              (valueBytes ++ addressBytes) with
          | .final event => (some (.finalFfi event), callEnv [] state)
          | .returned newFfi _ => (none, { state with ffi := newFfi })
        else (some .error, state)
      else
        if state.shMdomain (riscvByteAlignHOL (width := width) address) then
          match callFfi state.ffi (.sharedMem .mappedWrite)
              (loopShMemByteCount byteCount)
              (valueBytes.take byteCount ++ addressBytes) with
          | .final event => (some (.finalFfi event), callEnv [] state)
          | .returned newFfi _ => (none, { state with ffi := newFfi })
        else (some .error, state)
  | _ => (some .error, state)

/-- Width-generic exact dispatch port of HOL `loopSem$sh_mem_op_def`
    (`loopSemScript.sml:255-262`). -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "sh_mem_op_def"]
def shMemOpHOL {width : Nat} [NeZero width]
    (state : LoopMachineState (RiscV.Word width) F)
    (operator : CrepMemOp) (name : Nat) (address : RiscV.Word width) :
    LoopMachineStep (RiscV.Word width) F :=
  match operator with
  | .load => shMemLoadHOL state name address 0
  | .store => shMemStoreHOL state name address 0
  | .load8 => shMemLoadHOL state name address 1
  | .store8 => shMemStoreHOL state name address 1
  | .load16 => shMemLoadHOL state name address 2
  | .store16 => shMemStoreHOL state name address 2
  | .load32 => shMemLoadHOL state name address 4
  | .store32 => shMemStoreHOL state name address 4

/-! FLAPJACK-SPECIFIC (not exact tagged ports).  The following byte-array
    helpers are the 64-bit RISC-V instances of HOL's polymorphic word memory
    codec.  The exact width-generic ports are `readBytearrayHOL`,
    `memLoadByteAuxHOL`, `memStoreByteAuxHOL` and `writeBytearrayHOL` above; the
    definitions below are their `width := 64`, little-endian specializations
    using the reviewed RV64 codec.  They convert the machine's partial,
    `Bool`-valued memory/domain representation into HOL's total `word_loc` map
    and address set.  The width-polymorphic `ExtCall`/hook boundaries remain
    tracked by flapjack-s6a.3.3.1. -/

/-- HOL's total `'a word -> 'a word_loc` memory for a machine state: an absent
    address is HOL's `Loc` (not a `Word`), so byte loads/stores on it fail. -/
def loopTotalMemory (state : LoopMachineState (RiscV.Word 64) F) :
    RiscV.Word 64 → LoopValue (RiscV.Word 64) :=
  fun address => (state.memory address).getD (.loc 0 0)

/-- HOL's address set `dm` for a machine state. -/
def loopTotalDomain (state : LoopMachineState (RiscV.Word 64) F) :
    RiscV.Word 64 → Prop :=
  fun address => state.mdomain address = true

instance instDecidablePredLoopTotalDomain
    (state : LoopMachineState (RiscV.Word 64) F) :
    DecidablePred (loopTotalDomain state) :=
  fun address => (inferInstance : Decidable (state.mdomain address = true))

/-- 64-bit instance of HOL `mem_load_byte_aux_def` (`wordSemScript.sml:159`). -/
def loopMemLoadByteAux (state : LoopMachineState (RiscV.Word 64) F)
    (address : RiscV.Word 64) : Option UInt8 :=
  memLoadByteAuxHOL (width := 64) (loopTotalMemory state) (loopTotalDomain state)
    state.be address

/-- 64-bit instance of HOL `mem_store_byte_aux_def` (`wordSemScript.sml:171`). -/
def loopMemStoreByteAux (state : LoopMachineState (RiscV.Word 64) F)
    (address : RiscV.Word 64) (byte : UInt8) :
    Option (LoopMachineState (RiscV.Word 64) F) :=
  match memStoreByteAuxHOL (width := 64) (loopTotalMemory state)
      (loopTotalDomain state) state.be address byte with
  | some memory => some { state with memory := fun current => some (memory current) }
  | none => none

/-- 64-bit instance of HOL `read_bytearray_def` (`miscScript.sml:113`). -/
def loopReadByteArray (state : LoopMachineState (RiscV.Word 64) F)
    (address : RiscV.Word 64) : Nat → Option (List UInt8) :=
  fun length => readBytearrayHOL address length (loopMemLoadByteAux state)

/-- 64-bit instance of HOL `write_bytearray_def` (`wordSemScript.sml:178`).  As in
    HOL, a failed byte store leaves the original state unchanged. -/
def loopWriteByteArray (state : LoopMachineState (RiscV.Word 64) F)
    (address : RiscV.Word 64) : List UInt8 → LoopMachineState (RiscV.Word 64) F
  | bytes => { state with
      memory := fun current =>
        some (writeBytearrayHOL address bytes (loopTotalMemory state)
          (loopTotalDomain state) state.be current) }

/-! FLAPJACK-SPECIFIC (not an exact HOL port).  The `LoopEvaluateHooks.ffi`
    boundary for the source `ExtCall` case of `loopSem$evaluate_def`
    (`loopSemScript.sml:427-440`).  `evaluateLoop` has already applied
    `cut_state`, so the hook reads the four local pointers/lengths from the
    incoming state.  The exact polymorphic port is tracked by the dependency
    bead. -/
def loopMachineExtCall (state : LoopMachineState (RiscV.Word 64) F)
    (function : FunName) (configuration configurationLength array arrayLength : Nat) :
    LoopMachineStep (RiscV.Word 64) F :=
  match state.locals configurationLength, state.locals configuration,
      state.locals arrayLength, state.locals array with
  | some (.word configurationSize), some (.word configurationAddress),
    some (.word arraySize), some (.word arrayAddress) =>
      match loopReadByteArray state configurationAddress configurationSize.toNat,
          loopReadByteArray state arrayAddress arraySize.toNat with
      | some configurationBytes, some arrayBytes =>
          match callFfi state.ffi (.extCall function) configurationBytes arrayBytes with
          | .final event => (some (.finalFfi event), callEnv [] state)
          | .returned newFfi newBytes =>
              (none, { loopWriteByteArray state arrayAddress newBytes with ffi := newFfi })
      | _, _ => (some .error, state)
  | _, _, _, _ => (some .error, state)

/-- The `LoopEvaluateHooks.ffi` boundary.  The live set is ignored because
    `evaluateLoop` performs the `cut_state` before calling the hook. -/
def loopMachineFfiHook (state : LoopMachineState (RiscV.Word 64) F)
    (function : FunName) (configuration configurationLength array arrayLength : Nat)
    (_live : List Nat) : LoopMachineStep (RiscV.Word 64) F :=
  loopMachineExtCall state function configuration configurationLength array arrayLength

end Flapjack
