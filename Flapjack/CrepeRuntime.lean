import Flapjack.CrepeSemantics
import Flapjack.PanValueFfiSemantics

/-!
Observable runtime boundary for the Crepe evaluator.

`CrepeSemantics` is intentionally a compact executable model whose handlers
return either a new state or an observable terminal event.  CakeML's `crepSem`
has a richer machine state and the same observable `FinalFFI` result.  This
file ports that richer runtime boundary: it is the state/result vocabulary on
which the full compiler simulation can be built.

The FFI request carries the byte arrays produced by CakeML's
`read_bytearray`.  The concrete foreign-state type is deliberately left to
the handler, just as CakeML leaves `call_FFI` abstract.  The runtime still
keeps the memory domains, clock, endianness, and FFI state explicit.
-/

namespace Flapjack

/- A tiny Nat word-cell model used by the executable runtime fixtures.  The
   production evaluator receives a target's `PanMemoryModel`; this fixture
   keeps the existing Nat regression states explicit without smuggling in a
   whole target backend. -/
def natCrepRuntimeMemoryModel : PanMemoryModel Nat :=
  { byteAlign := fun _ address => address
    getByte := fun _ _ value _ => value
    setByte := fun _ _ value _ _ => value
    aligned := fun _ _ => true
    wordOfBytes := fun _ bytes =>
      match bytes with
      | value :: _ => value
      | [] => 0
    wordOp := fun _ _ => none
    compare := fun _ _ _ => 0
    shift := fun _ _ _ => none }

def natCrepRuntimeFfiContext : PanValueFfiContext Nat :=
  { sharedDomain := fun _ => true
    byteAlign := fun address => address
    bigEndian := false
    wordToBytes := fun value _ => [UInt8.ofNat value]
    wordOfBytes := fun _ bytes =>
      match bytes with
      | value :: _ => value.toNat
      | [] => 0
    wordToByte := fun value => UInt8.ofNat value
    byteToWord := fun value => value.toNat
    valueToNat := id }

structure CrepRuntimeState (α σ : Type u) where
  locals : Nat → Option α
  globals : α → Option α
  functions : List (CompiledFunction α)
  memory : α → Option α
  memaddrs : α → Bool
  shMemaddrs : α → Bool
  /-- The word-cell operations used by CakeML's `mem_load_byte` and
      `mem_load_32` (panSemScript.sml:86-137). -/
  memoryModel : PanMemoryModel α
  bytesInWord : α
  ffiContext : PanValueFfiContext α
  clock : Nat
  bigEndian : Bool
  ffi : σ
  baseAddress : α
  topAddress : α

/- Exact executable counterpart of CakeML Pancake's `dec_clock_def`
   (`crepSemScript.sml:145-148`).  The state is otherwise unchanged. -/
def decCrepClock (state : CrepRuntimeState α σ) : CrepRuntimeState α σ :=
  { state with clock := state.clock - 1 }

/- Exact executable counterpart of CakeML Pancake's `empty_locals_def`
   (`crepSemScript.sml:71`).  Terminal timeout and exception boundaries do not
   expose the caller's transient locals. -/
def clearCrepRuntimeLocals (state : CrepRuntimeState α σ) : CrepRuntimeState α σ :=
  { state with locals := fun _ => none }

inductive CrepRuntimeRequest (α : Type u) where
  | extCall (function : FunName)
      (configuration array : List UInt8)
  | sharedMem (operator : CrepMemOp) (name : Nat) (address : α)
      (payload : List UInt8)
  deriving DecidableEq, Repr

inductive CrepRuntimeFfiResponse (α σ ε : Type u) where
  | returned (state : CrepRuntimeState α σ) (bytes : List UInt8)
  | final (event : ε)

abbrev CrepRuntimeFfiHandler (α σ ε : Type u) :=
  CrepRuntimeRequest α → CrepRuntimeState α σ → CrepRuntimeFfiResponse α σ ε

inductive CrepRuntimeResult (α ε : Type u) where
  | normal
  | error
  | timeout
  | broke (label : Nat)
  | continued (label : Nat)
  | returned (values : List α)
  | raised (exception : α)
  | finalFfi (event : ε)
  deriving DecidableEq, Repr

abbrev CrepRuntimeStep (α σ ε : Type u) :=
  CrepRuntimeResult α ε × CrepRuntimeState α σ

def crepRuntimeMemWidth : CrepMemOp → Nat
  | .load | .store => 0
  | .load8 | .store8 => 1
  | .load16 | .store16 => 2
  | .load32 | .store32 => 4

def crepRuntimeSharedAddress (state : CrepRuntimeState α σ)
    (operator : CrepMemOp) (address : α) : α :=
  if crepRuntimeMemWidth operator = 0 then address
  else state.memoryModel.byteAlign state.bytesInWord address

def crepRuntimeSharedAddressValid (state : CrepRuntimeState α σ)
    (operator : CrepMemOp) (address : α) : Bool :=
  state.shMemaddrs (crepRuntimeSharedAddress state operator address)

def crepRuntimeLoad (state : CrepRuntimeState α σ) (address : α) : Option α :=
  if state.memaddrs address then state.memory address else none

def crepRuntimeLoadByte [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address : α) : Option α :=
  let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
  if state.memaddrs alignedAddress then do
    let value ← state.memory alignedAddress
    pure (state.memoryModel.getByte state.bytesInWord address value state.bigEndian)
  else none

def crepRuntimeLoad32 [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address : α) : Option α :=
  if state.memoryModel.aligned 4 address then
    let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
    if state.memaddrs alignedAddress then do
      let value ← state.memory alignedAddress
      pure (state.memoryModel.wordOfBytes state.bigEndian
        [state.memoryModel.getByte state.bytesInWord address value state.bigEndian,
         state.memoryModel.getByte state.bytesInWord (address + 1) value state.bigEndian,
         state.memoryModel.getByte state.bytesInWord (address + 1 + 1) value state.bigEndian,
         state.memoryModel.getByte state.bytesInWord (address + 1 + 1 + 1)
           value state.bigEndian])
    else none
  else none

def crepRuntimeStore [BEq α] (state : CrepRuntimeState α σ)
    (address value : α) : Option (CrepRuntimeState α σ) :=
  if state.memaddrs address then
    some { state with memory := updateMemory state.memory address value }
  else none

def crepRuntimeStoreByte [BEq α] [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address value : α) :
    Option (CrepRuntimeState α σ) :=
  let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
  if state.memaddrs alignedAddress then do
    let cell ← state.memory alignedAddress
    let updated := state.memoryModel.setByte state.bytesInWord address value cell state.bigEndian
    pure { state with memory := updateMemory state.memory alignedAddress updated }
  else none

def crepRuntimeStore32 [BEq α] [Add α] [OfNat α 0] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address value : α) :
    Option (CrepRuntimeState α σ) :=
  if state.memoryModel.aligned 4 address then
    let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
    if state.memaddrs alignedAddress then do
      let cell ← state.memory alignedAddress
      let cell0 := state.memoryModel.setByte state.bytesInWord address
        (state.memoryModel.getByte state.bytesInWord 0 value state.bigEndian)
        cell state.bigEndian
      let cell1 := state.memoryModel.setByte state.bytesInWord (address + 1)
        (state.memoryModel.getByte state.bytesInWord 1 value state.bigEndian)
        cell0 state.bigEndian
      let cell2 := state.memoryModel.setByte state.bytesInWord (address + 1 + 1)
        (state.memoryModel.getByte state.bytesInWord (1 + 1) value state.bigEndian)
        cell1 state.bigEndian
      let cell3 := state.memoryModel.setByte state.bytesInWord (address + 1 + 1 + 1)
        (state.memoryModel.getByte state.bytesInWord (1 + 1 + 1) value state.bigEndian)
        cell2 state.bigEndian
      pure { state with memory := updateMemory state.memory alignedAddress cell3 }
    else none
  else none

def crepRuntimeAssignExisting
    (locals : Nat → Option α) (names : List Nat) (values : List α) :
    Option (Nat → Option α) :=
  if names.length != values.length then none
  else if !names.all (fun name => (locals name).isSome) then none
  else if names.eraseDups.length != names.length then none
  else
    some ((names.zip values).foldl
      (fun locals (name, value) => updateCrepLocal locals name value) locals)

def crepRuntimeReadBytes [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address : α) : Nat → Option (List UInt8)
  | 0 => some []
  | length + 1 => do
      let value ← crepRuntimeLoadByte state address
      let rest ← crepRuntimeReadBytes state (address + 1) length
      pure (state.ffiContext.wordToByte value :: rest)
termination_by length => length

def crepRuntimeWriteBytes [BEq α] [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address : α) :
    List UInt8 → Option (CrepRuntimeState α σ)
  | [] => some state
  | byte :: bytes => do
      let tailState ← crepRuntimeWriteBytes state (address + 1) bytes
      match crepRuntimeStoreByte tailState address
          (state.ffiContext.byteToWord byte) with
      | some updatedState => some updatedState
      | none => some state
termination_by bytes => sizeOf bytes

def crepRuntimeExtCallValues [BEq α] [Add α] [OfNat α 1]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (function : FunName)
    (configuration configurationLength array arrayLength : α) :
    CrepRuntimeStep α σ ε :=
  match crepRuntimeReadBytes state configuration
      (state.ffiContext.valueToNat configurationLength),
      crepRuntimeReadBytes state array
        (state.ffiContext.valueToNat arrayLength) with
  | some configurationBytes, some arrayBytes =>
      match handler (.extCall function configurationBytes arrayBytes) state with
      | .returned state bytes =>
          match crepRuntimeWriteBytes state array bytes with
          | some state => (.normal, state)
          | none => (.error, state)
      | .final event => (.finalFfi event, state)
  | _, _ => (.error, state)

def crepRuntimeExtCall [BEq α] [Add α] [OfNat α 1]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    CrepRuntimeStep α σ ε :=
  match state.locals configuration, state.locals configurationLength,
      state.locals array, state.locals arrayLength with
  | some configuration, some configurationLength, some array, some arrayLength =>
      crepRuntimeExtCallValues handler state function configuration configurationLength
        array arrayLength
  | _, _, _, _ => (.error, state)

def crepRuntimeSharedMem (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (operator : CrepMemOp)
    (name : Nat) (address : α) : CrepRuntimeStep α σ ε :=
  if crepRuntimeSharedAddressValid state operator address then
    match operator with
    | .load | .load8 | .load16 | .load32 =>
        let payload := state.ffiContext.wordToBytes address false
        match handler (.sharedMem operator name address payload) state with
        | .returned state bytes =>
            let value := state.ffiContext.wordOfBytes state.ffiContext.bigEndian bytes
            (.normal, { state with locals := updateCrepLocal state.locals name value })
        | .final event => (.finalFfi event, clearCrepRuntimeLocals state)
    | .store | .store8 | .store16 | .store32 =>
        match state.locals name with
        | none => (.error, state)
        | some value =>
            let width := crepRuntimeMemWidth operator
            let valueBytes := state.ffiContext.wordToBytes value false
            let addressBytes := state.ffiContext.wordToBytes address false
            let payload :=
              if width = 0 then valueBytes ++ addressBytes
              else valueBytes.take width ++ addressBytes
            match handler (.sharedMem operator name address payload) state with
            | .returned state _ => (.normal, state)
            | .final event => (.finalFfi event, state)
  else
    (.error, state)

def crepRuntimeSharedMemExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (operator : CrepMemOp)
    (name : Nat) (address : CrepExp α) : CrepRuntimeStep α σ ε :=
  match evalCrepFullExp state.locals state.memory state.baseAddress
      state.topAddress address with
  | some address => crepRuntimeSharedMem handler state operator name address
  | none => (.error, state)

def crepRuntimeExtCallExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (function : FunName)
    (configuration configurationLength array arrayLength : CrepExp α) :
    CrepRuntimeStep α σ ε :=
  match evalCrepFullExp state.locals state.memory state.baseAddress
      state.topAddress configuration,
      evalCrepFullExp state.locals state.memory state.baseAddress
        state.topAddress configurationLength,
      evalCrepFullExp state.locals state.memory state.baseAddress
        state.topAddress array,
      evalCrepFullExp state.locals state.memory state.baseAddress
        state.topAddress arrayLength with
  | some configuration, some configurationLength, some array, some arrayLength =>
      crepRuntimeExtCallValues handler state function configuration configurationLength
        array arrayLength
  | _, _, _, _ => (.error, state)

def evalCrepRuntimeExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) : CrepExp α → Option α
  | .const value => some value
  | .var name => state.locals name
  | .load address => do
      let address ← evalCrepRuntimeExp state address
      crepRuntimeLoad state address
  | .load32 address => do
      let address ← evalCrepRuntimeExp state address
      crepRuntimeLoad32 state address
  | .loadByte address => do
      let address ← evalCrepRuntimeExp state address
      crepRuntimeLoadByte state address
  | .loadGlob address => state.globals address
  | .op operator [left, right] => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      pure (evalPanBinOp operator left right)
  | .crepOp .mul [left, right] => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      pure (left * right)
  | .cmp operator left right => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      pure (evalPanCmp operator left right)
  | .shift operator left right => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      evalPanShift operator left right
  | .baseAddr => some state.baseAddress
  | .topAddr => some state.topAddress
  | _ => none
termination_by expression => sizeOf expression

def evalCrepRuntimeExps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) : List (CrepExp α) → Option (List α)
  | [] => some []
  | expression :: expressions => do
      let value ← evalCrepRuntimeExp state expression
      let values ← evalCrepRuntimeExps state expressions
      pure (value :: values)
termination_by expressions => sizeOf expressions

def restoreCrepRuntimeStep (name : Nat) (oldValue : Option α) :
    CrepRuntimeStep α σ ε → CrepRuntimeStep α σ ε
  | (result, state) =>
      (result, { state with locals := restoreCrepLocal state.locals name oldValue })

def crepRuntimeCallerState (caller callee : CrepRuntimeState α σ) :
    CrepRuntimeState α σ :=
  { caller with
    globals := callee.globals
    functions := callee.functions
    memory := callee.memory
    memaddrs := callee.memaddrs
    shMemaddrs := callee.shMemaddrs
    clock := callee.clock
    ffiContext := callee.ffiContext
    bigEndian := callee.bigEndian
    ffi := callee.ffi
    baseAddress := callee.baseAddress
    topAddress := callee.topAddress }

/- CakeML's `fix_clock_def` clamps the post-command clock to the smaller of
   the old and new clocks.  Keeping this boundary explicit matters when a
   nested command or FFI handler returns a state with a stale clock. -/
def fixCrepRuntimeClock (oldState : CrepRuntimeState α σ) :
    CrepRuntimeStep α σ ε → CrepRuntimeStep α σ ε
  | (result, newState) =>
      (result, { newState with clock := min oldState.clock newState.clock })

mutual
  def evalCrepRuntimeCall
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α]
      [ShiftLeft α] [ShiftRight α] [LT α]
      [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (handler : CrepRuntimeFfiHandler α σ ε)
      (primitive : CrepPrimitiveHandler α) :
      Nat → CrepRuntimeState α σ →
        Option (List Nat × Option (α × CrepProg α)) → FunName →
        List (CrepExp α) → Option (CrepRuntimeStep α σ ε)
    | 0, _, _, _, _ => none
    | fuel + 1, caller, info, function, arguments =>
        match evalCrepRuntimeExps caller arguments with
        | none => some (.error, caller)
        | some values =>
            match lookupCompiledFunction function caller.functions with
            | none => some (.error, caller)
            | some (parameters, body) =>
                match assignCrepValues (fun _ => none) parameters values with
                | none => some (.error, caller)
                | some calleeLocals =>
                    if caller.clock = 0 then
                      some (.timeout, clearCrepRuntimeLocals caller)
                    else
                      let callee := decCrepClock
                        { caller with locals := calleeLocals }
                      match evalCrepRuntimeProg handler primitive fuel callee body with
                      | none => some (.error, callee)
                      | some (result, callee) =>
                          let callerState := crepRuntimeCallerState caller callee
                          match result with
                          | .normal => some (.normal, callerState)
                          | .returned values =>
                              match info with
                              | none =>
                                  some (.returned values, clearCrepRuntimeLocals callerState)
                              | some (destinations, _) =>
                                  match crepRuntimeAssignExisting
                                      caller.locals destinations values with
                                  | some locals =>
                                      some (.normal, { callerState with locals := locals })
                                  | none => some (.error, callerState)
                          | .raised exception =>
                              match info with
                              | some (_, some (caught, continuation)) =>
                                  if caught == exception then
                                    evalCrepRuntimeProg handler primitive fuel
                                      { callerState with locals := caller.locals } continuation
                                  else
                                    some (.raised exception, clearCrepRuntimeLocals callerState)
                              | _ => some (.raised exception, clearCrepRuntimeLocals callerState)
                          | .broke _label => some (.error, clearCrepRuntimeLocals callerState)
                          | .continued _label => some (.error, clearCrepRuntimeLocals callerState)
                          | .error => some (.error, clearCrepRuntimeLocals callerState)
                          | .timeout => some (.timeout, clearCrepRuntimeLocals callerState)
                          | .finalFfi event =>
                              some (.finalFfi event, clearCrepRuntimeLocals callerState)
    termination_by fuel _ _ _ _ => fuel

  def evalCrepRuntimeProg
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α]
      [ShiftLeft α] [ShiftRight α] [LT α]
      [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (handler : CrepRuntimeFfiHandler α σ ε)
      (primitive : CrepPrimitiveHandler α) :
      Nat → CrepRuntimeState α σ → CrepProg α →
        Option (CrepRuntimeStep α σ ε)
    | 0, _, _ => none
    | _fuel + 1, state, .skip => some (.normal, state)
    | fuel + 1, state, .dec name value body =>
        match evalCrepRuntimeExp state value with
        | none => some (.error, state)
        | some value =>
            let nextState := { state with locals := updateCrepLocal state.locals name value }
            match evalCrepRuntimeProg handler primitive fuel nextState body with
            | none => some (.error, state)
            | some result => some (restoreCrepRuntimeStep name (state.locals name) result)
    | _fuel + 1, state, .assign name value =>
        match evalCrepRuntimeExp state value with
        | none => some (.error, state)
        | some value =>
            match state.locals name with
            | some _ =>
                some (.normal, { state with locals := updateCrepLocal state.locals name value })
            | none => some (.error, state)
    | _fuel + 1, state, .primitive names operator arguments =>
        match arguments.mapM state.locals with
        | none => some (.error, state)
        | some arguments =>
            match primitive operator arguments with
            | none => some (.error, state)
            | some values =>
                match crepRuntimeAssignExisting state.locals names values with
                | some locals => some (.normal, { state with locals := locals })
                | none => some (.error, state)
    | _fuel + 1, state, .store address value =>
        match evalCrepRuntimeExp state address, evalCrepRuntimeExp state value with
        | some address, some value =>
            match crepRuntimeStore state address value with
            | some state => some (.normal, state)
            | none => some (.error, state)
        | _, _ => some (.error, state)
    | _fuel + 1, state, .store32 address value =>
        match evalCrepRuntimeExp state address, evalCrepRuntimeExp state value with
        | some address, some value =>
            match crepRuntimeStore32 state address value with
            | some state => some (.normal, state)
            | none => some (.error, state)
        | _, _ => some (.error, state)
    | _fuel + 1, state, .storeByte address value =>
        match evalCrepRuntimeExp state address, evalCrepRuntimeExp state value with
        | some address, some value =>
            match crepRuntimeStoreByte state address value with
            | some state => some (.normal, state)
            | none => some (.error, state)
        | _, _ => some (.error, state)
    | _fuel + 1, state, .storeGlob address value =>
        match evalCrepRuntimeExp state value with
        | some value =>
            some (.normal, { state with globals := updateMemory state.globals address value })
        | none => some (.error, state)
    | fuel + 1, state, .seq first second =>
        match evalCrepRuntimeProg handler primitive fuel state first with
        | none => some (.error, state)
        | some result =>
            let (result, state) := fixCrepRuntimeClock state result
            match result with
            | .normal =>
              match evalCrepRuntimeProg handler primitive fuel state second with
              | some result => some result
              | none => some (.error, state)
            | _ => some (result, state)
    | fuel + 1, state, .ite condition thenBranch elseBranch =>
        match evalCrepRuntimeExp state condition with
        | none => some (.error, state)
        | some conditionValue =>
            match evalCrepRuntimeProg handler primitive fuel state
              (if conditionValue != 0 then thenBranch else elseBranch) with
            | some result => some result
            | none => some (.error, state)
    | fuel + 1, state, .while condition body =>
        match evalCrepRuntimeExp state condition with
        | none => some (.error, state)
        | some conditionValue =>
            if conditionValue == 0 then
              some (.normal, state)
            else
              let decremented := decCrepClock state
              match evalCrepRuntimeProg handler primitive fuel decremented body with
              | none => some (.error, state)
              | some result =>
                  let (result, state) := fixCrepRuntimeClock decremented result
                  match result with
                  | .normal =>
                    match evalCrepRuntimeProg handler primitive fuel state
                    (.while condition body) with
                    | some result => some result
                    | none => some (.error, state)
                  | .continued 0 =>
                    match evalCrepRuntimeProg handler primitive fuel state
                      (.while condition body) with
                    | some result => some result
                    | none => some (.error, state)
                  | .broke 0 => some (.normal, state)
                  | .continued label => some (.continued (label - 1), state)
                  | .broke label => some (.broke (label - 1), state)
                  | result => some (result, state)
    | _fuel + 1, state, .break label => some (.broke label, state)
    | _fuel + 1, state, .continue label => some (.continued label, state)
    | fuel + 1, state, .call info function arguments =>
        evalCrepRuntimeCall handler primitive fuel state info function arguments
    | _fuel + 1, state, .extCall function configuration configurationLength array arrayLength =>
        some (crepRuntimeExtCall handler state function
          configuration configurationLength array arrayLength)
    | _fuel + 1, state, .raise exception =>
        some (.raised exception, clearCrepRuntimeLocals state)
    | _fuel + 1, state, .return values =>
        match evalCrepRuntimeExps state values with
        | some values => some (.returned values, clearCrepRuntimeLocals state)
        | none => some (.error, state)
    | _fuel + 1, state, .shMem operator name address =>
        match operator with
        | .load | .load8 | .load16 | .load32 =>
            match state.locals name with
            | some _ => some (crepRuntimeSharedMemExp handler state operator name address)
            | none => some (.error, state)
        | .store | .store8 | .store16 | .store32 =>
            match state.locals name with
            | some _ => some (crepRuntimeSharedMemExp handler state operator name address)
            | none => some (.error, state)
    | _fuel + 1, state, .tick =>
        if state.clock = 0 then some (.timeout, clearCrepRuntimeLocals state)
        else some (.normal, decCrepClock state)
    termination_by fuel _ _ => fuel
end

def evalCrepRuntimeResult
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (state : CrepRuntimeState α σ) (program : CrepProg α) :
    Option (CrepRuntimeResult α ε × CrepRuntimeState α σ) :=
  evalCrepRuntimeProg handler primitive fuel state program

theorem crepRuntimeLoad_memaddrs
    (state : CrepRuntimeState α σ) (address : α)
    (haddress : state.memaddrs address = true) :
    crepRuntimeLoad state address = state.memory address := by
  simp [crepRuntimeLoad, haddress]

theorem crepRuntimeStore_invalid
    [BEq α] (state : CrepRuntimeState α σ) (address value : α)
    (haddress : state.memaddrs address = false) :
    crepRuntimeStore state address value = none := by
  simp [crepRuntimeStore, haddress]

theorem evalCrepRuntimeResult_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ) :
    evalCrepRuntimeResult handler primitive (fuel + 1) state .skip =
      some (.normal, state) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg]

end Flapjack
