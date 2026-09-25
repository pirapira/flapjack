import Flapjack.Pancake.Semantics.CrepSem.Eval
import Flapjack.RiscV.PanMemory

/-!
# Total Crep evaluator fragment

This module gives total clock-based equations for `Skip`, `Break`, `Continue`,
`Tick`, `Assign`, `Store`, `ShMem`, `If`, `Seq`, `While`, `Return`, `Raise`,
`Dec`, and a restricted `Call` over its recursive syntax and the 11-field
`CrepHolState`. Call reads the state's code map and recursively executes
callee bodies which decode into this syntax; source bodies containing
`Primitive`, `Store32`, `StoreByte`, `StoreGlob`, or a call exception handler
remain outside this fragment. This is not a whole-program evaluator. The
result carrier is `option crepSem$result`, so ordinary completion is `none`
and control results retain their HOL constructors. The ShMem clause uses the executable
`FfiState`/`UInt8` carrier; its bridge to exact HOL `ffi_state`/`word8` remains
unclaimed.
-/

namespace Flapjack

/-- The four nonrecursive `evaluate_def` forms handled by this first total
    Crep evaluator slice. `toCrepProg` records their exact source constructors. -/
inductive CrepClockLeaf where
  | skip
  | breakAt (label : Nat)
  | continueAt (label : Nat)
  | tick
  deriving DecidableEq, Repr

/-- Embed a clock leaf into the production Crep syntax. -/
def CrepClockLeaf.toCrepProg {width : Nat} :
    CrepClockLeaf → CrepProg (BitVec width)
  | .skip => .skip
  | .breakAt label => .break label
  | .continueAt label => .continue label
  | .tick => .tick

/-- Recursive program fragment for the total clock/control evaluator. Its
    `Assign`, `Store`, `ShMem`, and `If` nodes evaluate source `CrepExp` terms
    in the current HOL state, and its `Seq` nodes use the HOL `fix_clock` boundary
    between recursively evaluated programs. `While` uses clock decrease and
    the same `fix_clock` boundary between iterations. Return nodes evaluate
    their expression list in the current HOL state. Its Call form reads the
    state's code map and only executes callees accepted by
    `CrepProg.toCrepClockProg?`; unsupported source constructors and handler
    continuations remain outside this fragment. -/
inductive CrepClockProg (width : Nat) where
  | leaf (value : CrepClockLeaf)
  | raiseException (value : BitVec width)
  | assignLocal (name : Nat) (value : CrepExp (BitVec width))
  | store (destination source : CrepExp (BitVec width))
  | sharedMemory (operator : CrepMemOp) (name : Nat)
      (address : CrepExp (BitVec width))
  | extCall (function : String)
      (configuration configurationLength array arrayLength : Nat)
  | decLocal (name : Nat) (value : CrepExp (BitVec width))
      (body : CrepClockProg width)
  | seq (first second : CrepClockProg width)
  | returnValues (values : List (CrepExp (BitVec width)))
  | call (returnNames : Option (List Nat))
      (function : FunName) (arguments : List (CrepExp (BitVec width)))
  | ite (condition : CrepExp (BitVec width))
      (thenBranch elseBranch : CrepClockProg width)
  | whileLoop (condition : CrepExp (BitVec width))
      (body : CrepClockProg width)

/-- Embed the restricted recursive syntax into production Crep syntax. -/
def CrepClockProg.toCrepProg {width : Nat} :
  CrepClockProg width → CrepProg (BitVec width)
  | .leaf value => value.toCrepProg
  | .raiseException value => .raise value
  | .assignLocal name value => .assign name value
  | .store destination source => .store destination source
  | .sharedMemory operator name address => .shMem operator name address
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function configuration configurationLength array arrayLength
  | .decLocal name value body => .dec name value body.toCrepProg
  | .seq first second => .seq first.toCrepProg second.toCrepProg
  | .returnValues values => .return values
  | .call returnNames function arguments =>
      .call (returnNames.map fun names => (names, none)) function arguments
  | .ite condition thenBranch elseBranch =>
      .ite condition thenBranch.toCrepProg elseBranch.toCrepProg
  | .whileLoop condition body => .while condition body.toCrepProg
termination_by program => sizeOf program
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [CrepClockProg.decLocal.sizeOf_spec,
        CrepClockProg.seq.sizeOf_spec, CrepClockProg.ite.sizeOf_spec,
        CrepClockProg.whileLoop.sizeOf_spec, CrepClockProg.call.sizeOf_spec]; omega)

/-- Decode the source code-map bodies covered by this restricted evaluator.
    Returning `none` keeps unsupported source constructors outside the exact
    Call claim instead of assigning them invented behavior. -/
def CrepProg.toCrepClockProg? {width : Nat} :
    CrepProg (BitVec width) → Option (CrepClockProg width)
  | .skip => some (.leaf .skip)
  | .break label => some (.leaf (.breakAt label))
  | .continue label => some (.leaf (.continueAt label))
  | .tick => some (.leaf .tick)
  | .raise value => some (.raiseException value)
  | .assign name value => some (.assignLocal name value)
  | .store destination source => some (.store destination source)
  | .shMem operator name address => some (.sharedMemory operator name address)
  | .extCall function configuration configurationLength array arrayLength =>
      some (.extCall function configuration configurationLength array arrayLength)
  | .dec name value body => do
      let body ← body.toCrepClockProg?
      pure (.decLocal name value body)
  | .seq first second => do
      let first ← first.toCrepClockProg?
      let second ← second.toCrepClockProg?
      pure (.seq first second)
  | .return values => some (.returnValues values)
  | .ite condition thenBranch elseBranch => do
      let thenBranch ← thenBranch.toCrepClockProg?
      let elseBranch ← elseBranch.toCrepClockProg?
      pure (.ite condition thenBranch elseBranch)
  | .while condition body => do
      let body ← body.toCrepClockProg?
      pure (.whileLoop condition body)
  | .call none function arguments => some (.call none function arguments)
  | .call (some (names, none)) function arguments =>
      some (.call (some names) function arguments)
  | .call (some (_, some _)) _ _ => none
  | .primitive .. | .store32 .. | .storeByte .. | .storeGlob .. => none
termination_by program => sizeOf program
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [CrepProg.dec.sizeOf_spec, CrepProg.seq.sizeOf_spec,
        CrepProg.ite.sizeOf_spec, CrepProg.while.sizeOf_spec,
        CrepProg.call.sizeOf_spec]; omega)

/-- HOL `exit_loop` on an optional control result: propagate other outcomes,
    while decrementing the nesting label of Break and Continue. -/
def exitCrepClockLoopResult {width : Nat} :
    Option (CrepResultHOL (BitVec width) FfiFinalEvent) →
      Option (CrepResultHOL (BitVec width) FfiFinalEvent)
  | some (.break label) => some (.break (label - 1))
  | some (.continue label) => some (.continue (label - 1))
  | result => result

/-- Little-endian byte projection used by HOL `word_to_bytes w F` at a fixed
    positive word width. HOL's `F` selects increasing-address, least
    significant byte first. -/
def crepClockWordToBytes {width : Nat} (word : BitVec width) : List UInt8 :=
  (List.range (width / 8)).map fun index =>
    UInt8.ofNat ((word.toNat / 2 ^ (8 * index)) % 256)

/-- HOL `word_of_bytes F 0w` over the same fixed-width word carrier. Bytes are
    installed in increasing-address order, so the first byte is least
    significant; `BitVec.ofNat` supplies HOL word truncation. -/
def crepClockWordOfBytes {width : Nat} (bytes : List UInt8) : BitVec width :=
  BitVec.ofNat width <| bytes.zipIdx.foldl
    (fun value (byte, index) => value + byte.toNat * 256 ^ index) 0

/-- Exact restricted-state ShMem clause from `crepSem$evaluate_def`, including
    the `sh_mem_op` width dispatch and `call_FFI` state transition. This helper
    handles only the ShMem constructor; it does not claim the full evaluator.
    Its state uses the executable `FfiState`/`UInt8` carrier and its result uses
    `FfiFinalEvent`; the exact `HolFfiState`/`word8` bridge is not asserted here,
    so this definition intentionally has no `@[hol]` tag. -/
def evalCrepClockShMem [NeZero width] {σ : Type _}
    (operator : CrepMemOp) (name : Nat)
    (addressExp : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ) :
    Option (CrepResultHOL (BitVec width) FfiFinalEvent) ×
      CrepHolState (BitVec width) σ :=
  match evalCrepHolExp state addressExp with
  | none => (some .error, state)
  | some address =>
      let byteCount := crepRuntimeMemWidth operator
      let sharedAddress :=
        if byteCount = 0 then address else holByteAlignBitVec address
      let inDomain := state.shMemaddrs sharedAddress
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          match state.locals name with
          | none => (some .error, state)
          | some _ =>
              if !inDomain then (some .error, state)
              else
                match callFfi state.ffi (.sharedMem .mappedRead)
                    [UInt8.ofNat byteCount] (crepClockWordToBytes address) with
                | .final event =>
                    (some (.finalFfi event), emptyCrepHolLocals state)
                | .returned ffi bytes =>
                    let withFfi := { state with ffi := ffi }
                    (none, setCrepHolVarW name
                      (.word (crepClockWordOfBytes bytes)) withFfi)
      | .store | .store8 | .store16 | .store32 =>
          match state.locals name with
          | some (.word value) =>
              if !inDomain then (some .error, state)
              else
                let valueBytes := crepClockWordToBytes value
                let addressBytes := crepClockWordToBytes address
                let payload :=
                  if byteCount = 0 then valueBytes ++ addressBytes
                  else valueBytes.take byteCount ++ addressBytes
                match callFfi state.ffi (.sharedMem .mappedWrite)
                    [UInt8.ofNat byteCount] payload with
                | .final event => (some (.finalFfi event), state)
                | .returned ffi _ => (none, { state with ffi := ffi })
          | _ => (some .error, state)

/-- Read a byte array from the state-owned memory map with the RISC-V byte
    model, source memory domain, and HOL endianness. -/
def crepClockReadByteArray [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (address : BitVec width)
    (length : Nat) : Option (List UInt8) :=
  (List.range length).mapM fun offset =>
    (crepHolEvalMemLoadByte
      (RiscV.panRiscVMemoryModelForEndian state.bigEndian)
      (BitVec.ofNat width (width / 8)) state
      (address + BitVec.ofNat width offset)).map fun byte => UInt8.ofNat byte.toNat

/-- Store one byte through `memaddrs` and the state's RISC-V word cell. HOL
    `mem_store_byte` returns `NONE` outside the domain, but `write_bytearray`
    keeps the recursively updated tail memory in that case. This helper thus
    leaves the supplied state unchanged when this byte cannot be stored. -/
def crepClockWriteByte [NeZero width] [BEq (BitVec width)] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (address : BitVec width)
    (byte : UInt8) : CrepHolState (BitVec width) σ := Id.run do
  let model := RiscV.panRiscVMemoryModelForEndian state.bigEndian
  let bytesInWord := BitVec.ofNat width (width / 8)
  let alignedAddress := model.byteAlign bytesInWord address
  if state.memaddrs alignedAddress then
    let .word value := state.memory alignedAddress
    let updated := model.setByte bytesInWord address
      (BitVec.ofNat width byte.toNat) value state.bigEndian
    return { state with memory := fun current =>
      if current == alignedAddress then .word updated else state.memory current }
  else
    return state

/-- HOL `write_bytearray` processes the tail first, then stores the head byte.
    Each failed store preserves the recursively updated memory passed to it. -/
def crepClockWriteByteArray [NeZero width] [BEq (BitVec width)] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (address : BitVec width)
    : List UInt8 → CrepHolState (BitVec width) σ
  | [] => state
  | byte :: bytes =>
      let writtenTail := crepClockWriteByteArray state
        (address + BitVec.ofNat width 1) bytes
      crepClockWriteByte writtenTail address byte

/-- Total isolated HOL `ExtCall` clause over a RISC-V `CrepHolState`. This
    boundary uses executable `FfiState`/`UInt8` and the fixed RISC-V byte
    model, so it intentionally has no `@[hol]` tag. Missing locals and failed
    reads return `Error` with the input state; returned bytes use HOL's
    tail-first `write_bytearray` state update. -/
def evalCrepClockExtCall [NeZero width] [BEq (BitVec width)] {σ : Type _}
    (function : String) (configuration configurationLength array arrayLength : Nat)
    (state : CrepHolState (BitVec width) σ) :
    Option (CrepResultHOL (BitVec width) FfiFinalEvent) ×
      CrepHolState (BitVec width) σ :=
  match state.locals configurationLength, state.locals configuration,
      state.locals arrayLength, state.locals array with
  | some (.word configLength), some (.word configAddress),
      some (.word arrayLengthValue), some (.word arrayAddress) =>
      match crepClockReadByteArray state configAddress configLength.toNat,
          crepClockReadByteArray state arrayAddress arrayLengthValue.toNat with
      | some configurationBytes, some arrayBytes =>
          match callFfi state.ffi (.extCall function) configurationBytes arrayBytes with
          | .final event => (some (.finalFfi event), state)
          | .returned ffi returnedBytes =>
              let withFfi := { state with ffi := ffi }
              (none, crepClockWriteByteArray withFfi arrayAddress returnedBytes)
      | _, _ => (some .error, state)
  | _, _, _, _ => (some .error, state)

/-- Merge the nonlocal fields returned by a code-map callee while retaining
    the caller's local environment, as `evaluate_def` does after `lookup_code`.
    This is evaluator infrastructure, not a whole-program theorem. -/
def crepClockCallerState {width : Nat} {σ : Type _}
    (caller callee : CrepHolState (BitVec width) σ) :
    CrepHolState (BitVec width) σ :=
  { caller with
    globals := callee.globals
    code := callee.code
    memory := callee.memory
    memaddrs := callee.memaddrs
    shMemaddrs := callee.shMemaddrs
    clock := callee.clock
    bigEndian := callee.bigEndian
    ffi := callee.ffi
    baseAddress := callee.baseAddress
    topAddress := callee.topAddress }

/-- Update a caller's existing return destinations after the Call result has
    been arity-checked. `none` records HOL's `FLOOKUP` failure. -/
def crepClockSetReturnLocals {width : Nat} {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (names : List Nat)
    (values : List (PanWordLab (BitVec width))) :
    Option (CrepHolState (BitVec width) σ) := do
  if names.length != values.length then none else
  let _ ← names.mapM state.locals
  let locals := (names.zip values).foldl
    (fun locals (name, value) candidate =>
      if name = candidate then some value else locals candidate) state.locals
  pure { state with locals := locals }

/-- The source call metadata admits only duplicate-free return destinations. -/
def crepClockCallInfoValid : Option (List Nat) → Bool
  | none => true
  | some destinations => destinations.eraseDups.length == destinations.length

/-- Total result/state equations for the matching HOL `evaluate_def` leaves,
    `Assign`, `Store`, `ShMem`, `If`, `Seq`, `While`, `Return`, `Raise`, and
    `Dec`, `ExtCall`, and restricted source-code-map `Call`. This restricted function deliberately has no
    `Option` fuel wrapper and does not depend on `evalCrepRuntimeResult`. -/
def evalCrepClockLeaf {width : Nat} {σ : Type _}
    (leaf : CrepClockLeaf) (state : CrepHolState (BitVec width) σ) :
    Option (CrepResultHOL (BitVec width) FfiFinalEvent) ×
      CrepHolState (BitVec width) σ :=
  match leaf with
  | .skip => (none, state)
  | .breakAt label => (some (.break label), state)
  | .continueAt label => (some (.continue label), state)
  | .tick =>
      if state.clock = 0 then
        (some .timeOut, emptyCrepHolLocals state)
      else
        (none, decCrepHolClock state)

/-- Total recursive evaluator for the implemented source-shaped Crep fragment.
    `Assign` requires an existing destination and uses HOL `set_var` on success;
    expression and destination errors preserve the input state. `If` selects
    the then branch for nonzero words and the else branch for zero. `Seq`
    applies HOL `fix_clock` between recursively evaluated programs. `While`
    recurs only after the HOL clock decrease and handles loop-control labels.
    No fuel,
    partial result, or branch-run assumption is exposed. Remaining constructors
    are not assigned behavior by this restricted evaluator.

    Source-reviewed disposition for HOL
    `eval_nested_assign_distinct_eq` (`pan_to_crepProofScript.sml:540`):
    despite sharing the Assign/Seq behavior, this is not the theorem's evaluator
    carrier. It executes production `CrepClockProg`/`CrepExp` over
    `CrepHolState`, while HOL `evaluate` consumes `CrepProgHOL`/`CrepExpHOL`
    and `CrepSemHOLState` with finite-support locals. A theorem using this
    evaluator would not state HOL's quantified theorem over `evaluate`; the
    exact Assign/nested-Seq evaluator and theorem port are tracked by
    `flapjack-4ac.5.82`, dependent on exact Crep carriers
    `flapjack-pxn.18.3.5.8.8`. -/
def evalCrepClockProg [NeZero width] {σ : Type _}
  : CrepClockProg width → CrepHolState (BitVec width) σ →
    Option (CrepResultHOL (BitVec width) FfiFinalEvent) ×
      CrepHolState (BitVec width) σ
  | .leaf value, state => evalCrepClockLeaf value state
  | .raiseException value, state =>
      (some (.exception value), emptyCrepHolLocals state)
  | .assignLocal name value, state =>
      match evalCrepHolExpWordLab state value with
      | none => (some .error, state)
      | some value =>
          match state.locals name with
          | none => (some .error, state)
          | some _ => (none, setCrepHolVarW name value state)
  | .store destination source, state =>
      match evalCrepHolExp state destination, evalCrepHolExp state source with
      | some address, some value =>
          if state.memaddrs address then
            (none, { state with memory := fun current =>
              if current = address then .word value else state.memory current })
          else (some .error, state)
      | _, _ => (some .error, state)
  | .sharedMemory operator name address, state =>
      evalCrepClockShMem operator name address state
  | .extCall function configuration configurationLength array arrayLength, state =>
      evalCrepClockExtCall function configuration configurationLength array arrayLength state
  | .decLocal name value body, state =>
      match evalCrepHolExpWordLab state value with
      | none => (some .error, state)
      | some value =>
          let oldValue := state.locals name
          let (result, bodyState) := evalCrepClockProg body
            (setCrepHolVarW name value state)
          (result, { bodyState with
            locals := resVarW bodyState.locals (name, oldValue) })
  | .seq first second, state =>
      match evalCrepClockProg first state with
      | (none, firstState) =>
          evalCrepClockProg second
            (fixCrepHolClockW state
              ((none : Option (CrepResultHOL (BitVec width) FfiFinalEvent)),
                firstState)).2
      | (some result, firstState) =>
          (some result, (fixCrepHolClockW state (some result, firstState)).2)
  | .returnValues values, state =>
      match values.mapM (evalCrepHolExpWordLab state) with
      | some words => (some (.return words), emptyCrepHolLocals state)
      | none => (some .error, state)
  | .call returnInfo function arguments, state =>
      match arguments.mapM (evalCrepHolExpWordLab state) with
      | none => (some .error, state)
      | some values =>
          match lookupCrepHolCode state.code function values values.length with
          | none => (some .error, state)
          | some (sourceBody, calleeLocals) =>
              if !crepClockCallInfoValid returnInfo then (some .error, state)
              else if state.clock = 0 then
                (some .timeOut, emptyCrepHolLocals state)
              else
                match sourceBody.toCrepClockProg? with
                | none => (some .error, state)
                | some body =>
                    let callee := decCrepHolClockW { state with locals := calleeLocals }
                    let (bodyResult, bodyState) := evalCrepClockProg body callee
                    let (bodyResult, bodyState) :=
                      fixCrepHolClockW callee (bodyResult, bodyState)
                    let callerState := crepClockCallerState state bodyState
                    match bodyResult with
                    | none => (some .error, bodyState)
                    | some (.break _) | some (.continue _) =>
                        (some .error, bodyState)
                    | some (.return values) =>
                        match returnInfo with
                        | none => (some (.return values), emptyCrepHolLocals bodyState)
                        | some destinations =>
                            match crepClockSetReturnLocals callerState destinations values with
                            | some updated => (none, updated)
                            | none => (some .error, bodyState)
                    | some (.exception exception) =>
                        (some (.exception exception), emptyCrepHolLocals bodyState)
                    | some result => (some result, emptyCrepHolLocals callerState)
  | .ite condition thenBranch elseBranch, state =>
      match evalCrepHolExp state condition with
      | some value =>
          if value = 0 then evalCrepClockProg elseBranch state
          else evalCrepClockProg thenBranch state
      | none => (some .error, state)
  | .whileLoop condition body, state =>
      match evalCrepHolExp state condition with
      | none => (some .error, state)
      | some value =>
          if value = 0 then (none, state)
          else if hclock : state.clock = 0 then
            (some .timeOut, emptyCrepHolLocals state)
          else
            let decState := decCrepHolClockW state
            let step := evalCrepClockProg body decState
            let fixed := fixCrepHolClockW decState step
            match hfixed : fixed with
            | (none, loopState) =>
                have hbound : loopState.clock ≤ decState.clock := by
                  have h := fixCrepHolClock_IMP_LESS_EQW decState step none loopState
                  exact h (by simpa [fixed] using hfixed)
                have hlt : loopState.clock < state.clock := by
                  simp [decState, decCrepHolClockW] at hbound
                  have hsub : state.clock - 1 < state.clock :=
                    Nat.sub_lt (Nat.pos_of_ne_zero hclock) (by omega)
                  exact Nat.lt_of_le_of_lt hbound hsub
                evalCrepClockProg (.whileLoop condition body) loopState
            | (some (.continue 0), loopState) =>
                have hbound : loopState.clock ≤ decState.clock := by
                  have h := fixCrepHolClock_IMP_LESS_EQW decState step
                    (some (.continue 0)) loopState
                  exact h (by simpa [fixed] using hfixed)
                have hlt : loopState.clock < state.clock := by
                  simp [decState, decCrepHolClockW] at hbound
                  have hsub : state.clock - 1 < state.clock :=
                    Nat.sub_lt (Nat.pos_of_ne_zero hclock) (by omega)
                  exact Nat.lt_of_le_of_lt hbound hsub
                evalCrepClockProg (.whileLoop condition body) loopState
            | (some (.break 0), loopState) => (none, loopState)
            | (result, loopState) => (exitCrepClockLoopResult result, loopState)
termination_by program state => (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    first
    | decreasing_trivial
    | (simp [setCrepHolVarW, decCrepHolClockW, fixCrepHolClockW] at *; omega)
    | (simp only [fixCrepHolClockW]; split <;> simp_wf <;>
        first | decreasing_trivial | omega)
  all_goals
    simp_wf
    simp [setCrepHolVarW, decCrepHolClockW, fixCrepHolClockW] at *
    omega

theorem evalCrepClockProg_return_success [NeZero width] {σ : Type _}
    (values : List (CrepExp (BitVec width)))
    (words : List (PanWordLab (BitVec width)))
    (state : CrepHolState (BitVec width) σ)
    (heval : values.mapM (evalCrepHolExpWordLab state) = some words) :
    evalCrepClockProg (.returnValues values) state =
      (some (.return words), emptyCrepHolLocals state) := by
  simp [evalCrepClockProg, heval]

theorem evalCrepClockProg_raise [NeZero width] {σ : Type _}
  (value : BitVec width) (state : CrepHolState (BitVec width) σ) :
    evalCrepClockProg (.raiseException value) state =
      (some (.exception value), emptyCrepHolLocals state) := by
  simp [evalCrepClockProg]

theorem evalCrepClockProg_assign_error [NeZero width] {σ : Type _}
    (name : Nat) (value : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (hvalue : evalCrepHolExpWordLab state value = none) :
    evalCrepClockProg (.assignLocal name value) state = (some .error, state) := by
  simp [evalCrepClockProg, hvalue]

theorem evalCrepClockProg_assign_missing [NeZero width] {σ : Type _}
    (name : Nat) (value : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (wordLab : PanWordLab (BitVec width))
    (hvalue : evalCrepHolExpWordLab state value = some wordLab)
    (hmissing : state.locals name = none) :
    evalCrepClockProg (.assignLocal name value) state = (some .error, state) := by
  simp [evalCrepClockProg, hvalue, hmissing]

theorem evalCrepClockProg_assign_success [NeZero width] {σ : Type _}
    (name : Nat) (value : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (wordLab : PanWordLab (BitVec width))
    (hvalue : evalCrepHolExpWordLab state value = some wordLab)
    (hbound : ∃ old, state.locals name = some old) :
    evalCrepClockProg (.assignLocal name value) state =
      (none, setCrepHolVarW name wordLab state) := by
  obtain ⟨old, hold⟩ := hbound
  simp [evalCrepClockProg, hvalue, hold]

theorem evalCrepClockProg_store_address_error [NeZero width] {σ : Type _}
    (destination source : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (haddress : evalCrepHolExp state destination = none) :
    evalCrepClockProg (.store destination source) state = (some .error, state) := by
  simp [evalCrepClockProg, haddress]

theorem evalCrepClockProg_store_value_error [NeZero width] {σ : Type _}
    (destination source : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ) (address : BitVec width)
    (haddress : evalCrepHolExp state destination = some address)
    (hsource : evalCrepHolExp state source = none) :
    evalCrepClockProg (.store destination source) state = (some .error, state) := by
  simp [evalCrepClockProg, haddress, hsource]

theorem evalCrepClockProg_store_domain_error [NeZero width] {σ : Type _}
    (destination source : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (address value : BitVec width)
    (haddress : evalCrepHolExp state destination = some address)
    (hsource : evalCrepHolExp state source = some value)
    (hdomain : state.memaddrs address = false) :
    evalCrepClockProg (.store destination source) state = (some .error, state) := by
  simp [evalCrepClockProg, haddress, hsource, hdomain]

theorem evalCrepClockProg_store_success [NeZero width] {σ : Type _}
    (destination source : CrepExp (BitVec width))
    (state : CrepHolState (BitVec width) σ)
    (address value : BitVec width)
    (haddress : evalCrepHolExp state destination = some address)
    (hsource : evalCrepHolExp state source = some value)
    (hdomain : state.memaddrs address = true) :
    evalCrepClockProg (.store destination source) state =
      (none, { state with memory := fun current =>
        if current = address then .word value else state.memory current }) := by
  simp [evalCrepClockProg, haddress, hsource, hdomain]

theorem evalCrepClockProg_dec_error [NeZero width] {σ : Type _}
    (name : Nat) (value : CrepExp (BitVec width))
    (body : CrepClockProg width) (state : CrepHolState (BitVec width) σ)
    (hvalue : evalCrepHolExpWordLab state value = none) :
    evalCrepClockProg (.decLocal name value body) state = (some .error, state) := by
  simp [evalCrepClockProg, hvalue]

theorem evalCrepClockProg_dec_success [NeZero width] {σ : Type _}
    (name : Nat) (value : CrepExp (BitVec width))
    (body : CrepClockProg width) (state : CrepHolState (BitVec width) σ)
    (wordLab : PanWordLab (BitVec width))
    (hvalue : evalCrepHolExpWordLab state value = some wordLab) :
    evalCrepClockProg (.decLocal name value body) state =
      let oldValue := state.locals name
      let (result, bodyState) :=
        evalCrepClockProg body (setCrepHolVarW name wordLab state)
      (result, { bodyState with locals := resVarW bodyState.locals (name, oldValue) }) := by
  simp [evalCrepClockProg, hvalue]

theorem evalCrepClockProg_return_error [NeZero width] {σ : Type _}
    (values : List (CrepExp (BitVec width)))
    (state : CrepHolState (BitVec width) σ)
    (heval : values.mapM (evalCrepHolExpWordLab state) = none) :
    evalCrepClockProg (.returnValues values) state = (some .error, state) := by
  simp [evalCrepClockProg, heval]

theorem evalCrepClockProg_seq_normal [NeZero width] {σ : Type _}
    (first second : CrepClockProg width)
    (state firstState : CrepHolState (BitVec width) σ)
    (hfirst : evalCrepClockProg first state = (none, firstState)) :
    evalCrepClockProg (.seq first second) state =
      evalCrepClockProg second
        (fixCrepHolClockW state
          ((none : Option (CrepResultHOL (BitVec width) FfiFinalEvent)),
            firstState)).2 := by
  simp [evalCrepClockProg, hfirst]

theorem evalCrepClockProg_seq_control [NeZero width] {σ : Type _}
    (first second : CrepClockProg width)
    (state firstState : CrepHolState (BitVec width) σ)
    (result : CrepResultHOL (BitVec width) FfiFinalEvent)
    (hfirst : evalCrepClockProg first state = (some result, firstState)) :
    evalCrepClockProg (.seq first second) state =
      (some result, (fixCrepHolClockW state (some result, firstState)).2) := by
  simp [evalCrepClockProg, hfirst]

theorem evalCrepClockProg_seq_skip_break [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (label : Nat) :
    evalCrepClockProg (.seq (.leaf .skip) (.leaf (.breakAt label))) state =
      (some (.break label), state) := by
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW]

theorem evalCrepClockProg_seq_break_stops [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (label nextLabel : Nat) :
    evalCrepClockProg
        (.seq (.leaf (.breakAt label)) (.leaf (.breakAt nextLabel))) state =
      (some (.break label), state) := by
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW]

theorem evalCrepClockProg_seq_tick_zero [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock = 0) :
    evalCrepClockProg (.seq (.leaf .tick) (.leaf .skip)) state =
      (some .timeOut, emptyCrepHolLocals state) := by
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW,
    emptyCrepHolLocals, hclock]

theorem evalCrepClockProg_seq_tick_positive [NeZero width] {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock ≠ 0) :
    evalCrepClockProg (.seq (.leaf .tick) (.leaf .skip)) state =
      (none, decCrepHolClock state) := by
  have hnot : ¬ state.clock < state.clock - 1 := by omega
  simp [evalCrepClockProg, evalCrepClockLeaf, fixCrepHolClockW,
    decCrepHolClock, hclock, hnot]

@[simp] theorem evalCrepClockLeaf_skip {width : Nat} {σ : Type _}
    (state : CrepHolState (BitVec width) σ) :
    evalCrepClockLeaf .skip state = (none, state) := rfl

@[simp] theorem evalCrepClockLeaf_break {width : Nat} {σ : Type _}
    (label : Nat) (state : CrepHolState (BitVec width) σ) :
    evalCrepClockLeaf (.breakAt label) state = (some (.break label), state) := rfl

@[simp] theorem evalCrepClockLeaf_continue {width : Nat} {σ : Type _}
    (label : Nat) (state : CrepHolState (BitVec width) σ) :
    evalCrepClockLeaf (.continueAt label) state =
      (some (.continue label), state) := rfl

theorem evalCrepClockLeaf_tick_zero {width : Nat} {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock = 0) :
    evalCrepClockLeaf .tick state =
      (some .timeOut, emptyCrepHolLocals state) := by
  simp [evalCrepClockLeaf, hclock]

theorem evalCrepClockLeaf_tick_positive {width : Nat} {σ : Type _}
    (state : CrepHolState (BitVec width) σ) (hclock : state.clock ≠ 0) :
    evalCrepClockLeaf .tick state = (none, decCrepHolClock state) := by
  simp [evalCrepClockLeaf, hclock]

theorem evalCrepClockProg_ite_zero [NeZero width] {σ : Type _}
    (condition : CrepExp (BitVec width)) (thenBranch elseBranch : CrepClockProg width)
    (state : CrepHolState (BitVec width) σ)
    (hcondition : evalCrepHolExp state condition = some 0) :
    evalCrepClockProg (.ite condition thenBranch elseBranch) state =
      evalCrepClockProg elseBranch state := by
  simp [evalCrepClockProg, hcondition]

theorem evalCrepClockProg_ite_nonzero [NeZero width] {σ : Type _}
    (condition : CrepExp (BitVec width)) (thenBranch elseBranch : CrepClockProg width)
    (state : CrepHolState (BitVec width) σ) (value : BitVec width)
    (hcondition : evalCrepHolExp state condition = some value) (hnonzero : value ≠ 0) :
    evalCrepClockProg (.ite condition thenBranch elseBranch) state =
      evalCrepClockProg thenBranch state := by
  simp only [evalCrepClockProg, hcondition]
  by_cases hzero : value = 0
  · exact False.elim (hnonzero hzero)
  · rw [if_neg hzero]

theorem evalCrepClockProg_ite_error [NeZero width] {σ : Type _}
    (condition : CrepExp (BitVec width)) (thenBranch elseBranch : CrepClockProg width)
    (state : CrepHolState (BitVec width) σ)
    (hcondition : evalCrepHolExp state condition = none) :
    evalCrepClockProg (.ite condition thenBranch elseBranch) state =
      (some .error, state) := by
  simp [evalCrepClockProg, hcondition]

end Flapjack
