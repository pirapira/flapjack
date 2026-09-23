import Flapjack.CrepeSemantics
import Flapjack.FiniteMap.Basic
import Flapjack.HolRef
import Flapjack.PanValueFfiSemantics

/-!
Observable runtime boundary for the Crepe evaluator.

`CrepeSemantics` is intentionally a compact executable model whose handlers
return either a new state or an observable terminal event.  CakeML's `crepSem`
has a richer machine state and the same observable `FinalFFI` result.  This
file ports that richer runtime boundary: it is the state/result vocabulary on
which the full compiler simulation can be built.

The FFI request carries the byte arrays produced by CakeML's
`read_bytearray`.  A handler receives only the concrete `FfiState` and may
return only its successor plus bytes, matching CakeML's `call_FFI` boundary;
the runtime itself applies the prescribed memory/local updates.  The runtime
still keeps the memory domains, clock, endianness, and FFI state explicit.
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
    wordOp := fun operator values =>
      match operator with
      | .add => some (values.foldr (fun left right => left + right) 0)
      | .sub =>
          match values with
          | [left, right] => some (left - right)
          | _ => none
      | .and | .or | .xor => none
    compare := fun operator left right => evalPanCmp operator left right
    shift := fun operator left right => evalPanShift operator left right }

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

def natCrepRuntimeFfiOracle : FfiOracle Unit :=
  fun _ state _ bytes => .returned state bytes

def natCrepRuntimeFfiState : FfiState Unit :=
  { oracle := natCrepRuntimeFfiOracle
    state := ()
    ioEvents := [] }

structure CrepRuntimeState (α σ : Type u) where
  /-- HOL `crepSem$state.locals` is a finite map from `varname` to `word_lab`.
      Lean's function representation is extensionally the same finite map;
      `PanWordLab.word` retains the HOL cell wrapper. -/
  locals : Nat → Option (PanWordLab α)
  /-- HOL `crepSem$state.globals` is a finite map from `5 word` to `word_lab`.
      Lean's function representation is extensionally the same finite map;
      `PanWordLab.word` retains the HOL cell wrapper. -/
  globals : BitVec 5 → Option (PanWordLab α)
  /-- HOL `crepSem$state.code`: the code map used by runtime function calls. -/
  code : FunName → Option (List Nat × CrepProg α)
  /-- HOL `crepSem$state.memory` is a total `'a word → 'a word_lab` function
      guarded by `memaddrs`; `PanWordLab.word` retains the HOL cell wrapper. -/
  memory : α → PanWordLab α
  memaddrs : α → Bool
  shMemaddrs : α → Bool
  /-- The word-cell operations used by CakeML's `mem_load_byte` and
      `mem_load_32` (panSemScript.sml:86-137). -/
  memoryModel : PanMemoryModel α
  bytesInWord : α
  ffiContext : PanValueFfiContext α
  clock : Nat
  bigEndian : Bool
  ffi : FfiState σ
  baseAddress : α
  topAddress : α

/- Flapjack clock update. Its field operation follows CakeML Pancake's
   `dec_clock_def`, but this runtime state still carries extra memory-model
   and FFI-context fields, so this is not tagged as an exact HOL definition. -/
def decCrepClock (state : CrepRuntimeState α σ) : CrepRuntimeState α σ :=
  { state with clock := state.clock - 1 }

def updateCrepRuntimeGlobal (globals : BitVec 5 → Option (PanWordLab α))
    (key : BitVec 5) (value : PanWordLab α) : BitVec 5 → Option (PanWordLab α) :=
  fun candidate => if key == candidate then some value else globals candidate

/-- Flapjack runtime adaptation of HOL `set_globals`: the 5-bit key and
    `word_lab` cell update agree, but the enclosing state still carries extra
    runtime fields, so this declaration is not an exact HOL port. -/
def setCrepRuntimeGlobals (key : BitVec 5) (value : PanWordLab α)
    (state : CrepRuntimeState α σ) : CrepRuntimeState α σ :=
  { state with globals := updateCrepRuntimeGlobal state.globals key value }

def updateCrepRuntimeLocal (locals : Nat → Option (PanWordLab α))
    (name : Nat) (value : PanWordLab α) : Nat → Option (PanWordLab α) :=
  fun candidate => if name == candidate then some value else locals candidate

/-- Flapjack update of the total HOL-shaped memory function. -/
def updateCrepRuntimeMemory [BEq α] (memory : α → PanWordLab α)
    (address : α) (value : PanWordLab α) : α → PanWordLab α :=
  fun candidate => if candidate == address then value else memory candidate

/- Flapjack local-clear operation. Its locals projection matches CakeML's
   `empty_locals_def` (`crepSemScript.sml:71`), but the enclosing state type
   still differs. Terminal timeout and exception boundaries do not expose
   the caller's transient locals. -/
def clearCrepRuntimeLocals (state : CrepRuntimeState α σ) : CrepRuntimeState α σ :=
  { state with locals := fun _ => none }

/-- Flapjack-only projection lemma for the local-clear operation. -/
@[simp] theorem clearCrepRuntimeLocals_code (state : CrepRuntimeState α σ) :
    (clearCrepRuntimeLocals state).code = state.code := rfl

/-- `upd_locals` for callee parameters on the emitted `word_lab` cells: each
    bound value is wrapped with `PanWordLab.word`, exactly as HOL's cell type. -/
def assignCrepRuntimeLocals (locals : Nat → Option (PanWordLab α))
    (names : List Nat) (values : List α) :
    Option (Nat → Option (PanWordLab α)) :=
  if names.length != values.length then none
  else
    some ((names.zip values).foldl
      (fun locals (name, value) => updateCrepRuntimeLocal locals name (.word value))
      locals)

def lookupCrepRuntimeCode [BEq String] (name : FunName) (values : List α)
    (code : FunName → Option (List Nat × CrepProg α)) :
    Option (CrepProg α × (Nat → Option (PanWordLab α))) :=
  match FLOOKUP code name with
  | none => none
  | some (parameters, body) =>
      if parameters.length == values.length &&
          parameters.eraseDups.length == parameters.length then
        match assignCrepRuntimeLocals (fun _ => none) parameters values with
        | some locals => some (body, locals)
        | none => none
      else none

inductive CrepRuntimeRequest (α : Type u) where
  | extCall (function : FunName)
      (configuration array : List UInt8)
  | sharedMem (operator : CrepMemOp) (name : Nat) (address : α)
      (payload : List UInt8)
  deriving DecidableEq, Repr

inductive CrepRuntimeFfiResponse (σ ε : Type u) where
  | returned (ffi : FfiState σ) (bytes : List UInt8)
  | final (event : ε)

abbrev CrepRuntimeFfiHandler (α σ ε : Type u) :=
  CrepRuntimeRequest α → FfiState σ → CrepRuntimeFfiResponse σ ε

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
  if state.memaddrs address then some (panTheWord (state.memory address)) else none

def crepRuntimeLoadByte [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address : α) : Option α :=
  let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
  if state.memaddrs alignedAddress then
    pure (state.memoryModel.getByte state.bytesInWord address
      (panTheWord (state.memory alignedAddress)) state.bigEndian)
  else none

def crepRuntimeLoad32 [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address : α) : Option α :=
  if state.memoryModel.aligned 4 address then
    let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
    if state.memaddrs alignedAddress then
      let value := panTheWord (state.memory alignedAddress)
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
    some { state with memory := updateCrepRuntimeMemory state.memory address (.word value) }
  else none

def crepRuntimeStoreByte [BEq α] [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address value : α) :
    Option (CrepRuntimeState α σ) :=
  let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
  if state.memaddrs alignedAddress then
    let cell := panTheWord (state.memory alignedAddress)
    let updated := state.memoryModel.setByte state.bytesInWord address value cell state.bigEndian
    pure { state with memory := updateCrepRuntimeMemory state.memory alignedAddress (.word updated) }
  else none

def crepRuntimeStore32 [BEq α] [Add α] [OfNat α 0] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address value : α) :
    Option (CrepRuntimeState α σ) :=
  if state.memoryModel.aligned 4 address then
    let alignedAddress := state.memoryModel.byteAlign state.bytesInWord address
    if state.memaddrs alignedAddress then
      let cell := panTheWord (state.memory alignedAddress)
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
      pure { state with memory := updateCrepRuntimeMemory state.memory alignedAddress (.word cell3) }
    else none
  else none

/-- Flapjack-only view of the total HOL-shaped memory as an `Option`-valued
    function (`some` of the carried word). This reconciles the production total
    `word_lab` memory with the `Option`-valued RISC-V pan memory model; the
    `word_lab` cell has a single constructor, so no cell is dropped. -/
def crepRuntimeMemoryView (memory : α → PanWordLab α) : α → Option α :=
  fun address => some (panTheWord (memory address))

theorem crepRuntimeMemoryView_updateCrepRuntimeMemory_word [BEq α]
    (memory : α → PanWordLab α) (address : α) (value : α) :
    crepRuntimeMemoryView (updateCrepRuntimeMemory memory address (.word value)) =
      updateMemory (crepRuntimeMemoryView memory) address value := by
  funext current
  by_cases hsame : current == address <;>
    simp [crepRuntimeMemoryView, updateCrepRuntimeMemory, updateMemory, panTheWord, hsame]

/-- Flapjack-only: memory-level view of a production word store. -/
theorem crepRuntimeStore_eq_memory_view [BEq α]
    (state : CrepRuntimeState α σ) (address value : α) :
    (crepRuntimeStore state address value).map (fun s => crepRuntimeMemoryView s.memory) =
      if state.memaddrs address then
        some (updateMemory (crepRuntimeMemoryView state.memory) address value) else none := by
  rw [crepRuntimeStore]
  by_cases h : state.memaddrs address = true
  · rw [if_pos h, if_pos h]
    simp only [Option.map_some]
    exact congrArg some
      (crepRuntimeMemoryView_updateCrepRuntimeMemory_word state.memory address value)
  · rw [if_neg h, if_neg h]
    rfl

/-- Flapjack-only: memory-level view of a production byte store. -/
theorem crepRuntimeStoreByte_eq_memory_view [BEq α] [Add α] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address value : α) :
    (crepRuntimeStoreByte state address value).map (fun s => crepRuntimeMemoryView s.memory) =
      if state.memaddrs (state.memoryModel.byteAlign state.bytesInWord address) then
        some (updateMemory (crepRuntimeMemoryView state.memory)
          (state.memoryModel.byteAlign state.bytesInWord address)
          (state.memoryModel.setByte state.bytesInWord address value
            (panTheWord (state.memory (state.memoryModel.byteAlign state.bytesInWord address)))
            state.bigEndian)) else none := by
  simp only [crepRuntimeStoreByte]
  by_cases h : state.memaddrs (state.memoryModel.byteAlign state.bytesInWord address) = true
  · rw [if_pos h, if_pos h]
    simp only [Option.pure_def, Option.map_some]
    exact congrArg some
      (crepRuntimeMemoryView_updateCrepRuntimeMemory_word state.memory _ _)
  · rw [if_neg h, if_neg h]
    rfl

/-- Flapjack-only: memory-level view of a production 32-bit store. -/
theorem crepRuntimeStore32_eq_memory_view [BEq α] [Add α] [OfNat α 0] [OfNat α 1]
    (state : CrepRuntimeState α σ) (address value : α) :
    (crepRuntimeStore32 state address value).map (fun s => crepRuntimeMemoryView s.memory) =
      if state.memoryModel.aligned 4 address then
        (if state.memaddrs (state.memoryModel.byteAlign state.bytesInWord address) then
          some (updateMemory (crepRuntimeMemoryView state.memory)
            (state.memoryModel.byteAlign state.bytesInWord address)
            (state.memoryModel.setByte state.bytesInWord (address + 1 + 1 + 1)
              (state.memoryModel.getByte state.bytesInWord (1 + 1 + 1) value state.bigEndian)
              (state.memoryModel.setByte state.bytesInWord (address + 1 + 1)
                (state.memoryModel.getByte state.bytesInWord (1 + 1) value state.bigEndian)
                (state.memoryModel.setByte state.bytesInWord (address + 1)
                  (state.memoryModel.getByte state.bytesInWord 1 value state.bigEndian)
                  (state.memoryModel.setByte state.bytesInWord address
                    (state.memoryModel.getByte state.bytesInWord 0 value state.bigEndian)
                    (panTheWord (state.memory (state.memoryModel.byteAlign state.bytesInWord address)))
                    state.bigEndian) state.bigEndian) state.bigEndian) state.bigEndian))
        else none)
      else none := by
  simp only [crepRuntimeStore32]
  by_cases ha : state.memoryModel.aligned 4 address = true
  · rw [if_pos ha, if_pos ha]
    by_cases hb : state.memaddrs (state.memoryModel.byteAlign state.bytesInWord address) = true
    · rw [if_pos hb, if_pos hb]
      simp only [Option.pure_def, Option.map_some]
      exact congrArg some
        (crepRuntimeMemoryView_updateCrepRuntimeMemory_word state.memory _ _)
    · rw [if_neg hb, if_neg hb]
      rfl
  · rw [if_neg ha, if_neg ha]
    rfl

/-- Flapjack-only: the single-constructor `word_lab` cell is recovered by
    re-wrapping its carried word. -/
theorem panWordLab_word_panTheWord (cell : PanWordLab α) :
    PanWordLab.word (panTheWord cell) = cell := by
  cases cell
  rfl

/-- Flapjack-only: re-totalize an `Option`-valued view into the production total
    memory, using `fallback` for cells the view does not carry. Since the
    production cell has a single constructor, a view that came from a total
    memory round-trips exactly. -/
def crepRuntimeMemoryOfView (view : α → Option α)
    (fallback : α → PanWordLab α) : α → PanWordLab α :=
  fun address => match view address with
    | some value => .word value
    | none => fallback address

theorem crepRuntimeMemoryOfView_view (memory : α → PanWordLab α) :
    crepRuntimeMemoryOfView (crepRuntimeMemoryView memory) memory = memory := by
  funext address
  simp only [crepRuntimeMemoryView, crepRuntimeMemoryOfView]
  rw [panWordLab_word_panTheWord]

theorem crepRuntimeMemoryOfView_updateMemory_word [BEq α]
    (memory : α → PanWordLab α) (address value : α) :
    crepRuntimeMemoryOfView
        (updateMemory (crepRuntimeMemoryView memory) address value) memory =
      updateCrepRuntimeMemory memory address (.word value) := by
  funext current
  by_cases hsame : current == address
  · simp [crepRuntimeMemoryOfView, updateMemory, updateCrepRuntimeMemory, hsame]
  · simp [crepRuntimeMemoryOfView, updateMemory, updateCrepRuntimeMemory,
      crepRuntimeMemoryView, hsame, panWordLab_word_panTheWord]

def crepRuntimeAssignExisting
    (locals : Nat → Option (PanWordLab α)) (names : List Nat) (values : List α) :
    Option (Nat → Option (PanWordLab α)) :=
  if names.length != values.length then none
  else if !names.all (fun name => (locals name).isSome) then none
  else if names.eraseDups.length != names.length then none
  else
    some ((names.zip values).foldl
      (fun locals (name, value) => updateCrepRuntimeLocal locals name (.word value))
      locals)

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
      match handler (.extCall function configurationBytes arrayBytes) state.ffi with
      | .returned ffi bytes =>
          let state := { state with ffi := ffi }
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
  match (state.locals configuration).map panTheWord,
      (state.locals configurationLength).map panTheWord,
      (state.locals array).map panTheWord,
      (state.locals arrayLength).map panTheWord with
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
        match handler (.sharedMem operator name address payload) state.ffi with
        | .returned ffi bytes =>
            let value := state.ffiContext.wordOfBytes false bytes
            let state := { state with ffi := ffi }
            (.normal, { state with locals := updateCrepRuntimeLocal state.locals name (.word value) })
        | .final event => (.finalFfi event, clearCrepRuntimeLocals state)
    | .store | .store8 | .store16 | .store32 =>
        match (state.locals name).map panTheWord with
        | none => (.error, state)
        | some value =>
            let width := crepRuntimeMemWidth operator
            let valueBytes := state.ffiContext.wordToBytes value false
            let addressBytes := state.ffiContext.wordToBytes address false
            let payload :=
              if width = 0 then valueBytes ++ addressBytes
              else valueBytes.take width ++ addressBytes
            match handler (.sharedMem operator name address payload) state.ffi with
            | .returned ffi _ => (.normal, { state with ffi := ffi })
            | .final event => (.finalFfi event, state)
  else
    (.error, state)

def evalCrepRuntimeExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) : CrepExp α → Option α
  | .const value => some value
  | .var name => (state.locals name).map panTheWord
  | .load address => do
      let address ← evalCrepRuntimeExp state address
      crepRuntimeLoad state address
  | .load32 address => do
      let address ← evalCrepRuntimeExp state address
      crepRuntimeLoad32 state address
  | .loadByte address => do
      let address ← evalCrepRuntimeExp state address
      crepRuntimeLoadByte state address
  | .loadGlob address => (state.globals address).map panTheWord
  | .op operator expressions => do
      let values ← expressions.mapM (evalCrepRuntimeExp state)
      state.memoryModel.wordOp operator values
  | .crepOp .mul [left, right] => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      pure (left * right)
  | .cmp operator left right => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      pure (state.memoryModel.compare operator left right)
  | .shift operator left right => do
      let left ← evalCrepRuntimeExp state left
      let right ← evalCrepRuntimeExp state right
      state.memoryModel.shift operator left right
  | .baseAddr => some state.baseAddress
  | .topAddr => some state.topAddress
  | _ => none
termination_by expression => sizeOf expression

/-! ### Word-result constructor slice

The equations below cover evaluator cases whose result shape does not depend
on HOL's `word_op`, `word_sh`, or byte-memory helpers. They are polymorphic in
the word carrier `α` and do not choose a RISC-V target. These are Flapjack-only
projection facts: `CrepRuntimeState` still has target fields absent from HOL's
`crepSem$state`, so they do not establish full evaluator correspondence. -/

/-- Projection equation for the `Const` case. This is Flapjack-only adapter
infrastructure: it wraps the raw production result as HOL's `word_lab`
constructor, while the full evaluator still uses a target-extended state. -/
theorem evalCrepRuntimeExp_const_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (value : α) :
    (evalCrepRuntimeExp state (.const value)).map PanWordLab.word =
      some (.word value) := by
  simp [evalCrepRuntimeExp]

/-- Projection equation for `Var`. Since `PanWordLab` has exactly the `word`
constructor, projecting and rewrapping the local cell recovers it. This is
Flapjack-only infrastructure, not a claim that its state type is HOL's. -/
theorem evalCrepRuntimeExp_var_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (name : Nat) :
    (evalCrepRuntimeExp state (.var name)).map PanWordLab.word = state.locals name := by
  cases h : state.locals name with
  | none => simp [evalCrepRuntimeExp, h]
  | some cell => cases cell <;> simp [evalCrepRuntimeExp, h, panTheWord]

/-- Projection equation for `LoadGlob`, independent of the target memory
model. This remains Flapjack-only because its state is target-extended. -/
theorem evalCrepRuntimeExp_loadGlob_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (address : BitVec 5) :
    (evalCrepRuntimeExp state (.loadGlob address)).map PanWordLab.word =
      state.globals address := by
  cases h : state.globals address with
  | none => simp [evalCrepRuntimeExp, h]
  | some cell => cases cell <;> simp [evalCrepRuntimeExp, h, panTheWord]

/-- The ordinary `Load` equation uses only the memory function and its domain
predicate. It assumes no byte order or canonical target, but is still an
adapter fact over Flapjack's extended state. -/
theorem evalCrepRuntimeExp_load_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) (address : CrepExp α) :
    (evalCrepRuntimeExp state (.load address)).map PanWordLab.word =
      (evalCrepRuntimeExp state address).bind fun value =>
        if state.memaddrs value then some (state.memory value) else none := by
  cases haddr : evalCrepRuntimeExp state address with
  | none => simp [evalCrepRuntimeExp, crepRuntimeLoad, haddr]
  | some value =>
    by_cases hdomain : state.memaddrs value
    · cases hmem : state.memory value with
      | word word => simp [evalCrepRuntimeExp, crepRuntimeLoad, haddr, hdomain, hmem, panTheWord]
    · simp [evalCrepRuntimeExp, crepRuntimeLoad, haddr, hdomain]

/-- Projection equation for `BaseAddr`; Flapjack-only because its state is
target-extended. -/
theorem evalCrepRuntimeExp_baseAddr_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) :
    (evalCrepRuntimeExp state .baseAddr).map PanWordLab.word =
      some (.word state.baseAddress) := by
  simp [evalCrepRuntimeExp]

/-- Projection equation for `TopAddr`; Flapjack-only because its state is
target-extended. -/
theorem evalCrepRuntimeExp_topAddr_wordLab
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state : CrepRuntimeState α σ) :
    (evalCrepRuntimeExp state .topAddr).map PanWordLab.word =
      some (.word state.topAddress) := by
  simp [evalCrepRuntimeExp]

def crepRuntimeSharedMemExp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (operator : CrepMemOp)
    (name : Nat) (address : CrepExp α) : CrepRuntimeStep α σ ε :=
  match evalCrepRuntimeExp state address with
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
  match evalCrepRuntimeExp state configuration,
      evalCrepRuntimeExp state configurationLength,
      evalCrepRuntimeExp state array,
      evalCrepRuntimeExp state arrayLength with
  | some configuration, some configurationLength, some array, some arrayLength =>
      crepRuntimeExtCallValues handler state function configuration configurationLength
        array arrayLength
  | _, _, _, _ => (.error, state)

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

def restoreCrepRuntimeStep (name : Nat) (oldValue : Option (PanWordLab α)) :
    CrepRuntimeStep α σ ε → CrepRuntimeStep α σ ε
  | (result, state) =>
      (result, { state with locals := fun candidate => if name == candidate then oldValue else state.locals candidate })

def crepRuntimeCallerState (caller callee : CrepRuntimeState α σ) :
    CrepRuntimeState α σ :=
  { caller with
    globals := callee.globals
    code := callee.code
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

def crepRuntimeCallInfoValid :
    Option (List Nat × Option (α × CrepProg α)) → Bool
  | none => true
  | some (destinations, _) =>
      destinations.eraseDups.length = destinations.length

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
            match lookupCrepRuntimeCode function values caller.code with
            | none => some (.error, caller)
            | some (body, calleeLocals) =>
                if !crepRuntimeCallInfoValid info then
                  some (.error, caller)
                else if caller.clock = 0 then
                  some (.timeout, clearCrepRuntimeLocals caller)
                else
                  let callee := decCrepClock
                    { caller with locals := calleeLocals }
                  match evalCrepRuntimeProg handler primitive fuel callee body with
                  | none => none
                  | some (result, callee) =>
                      let (result, callee) := fixCrepRuntimeClock callee (result, callee)
                      let callerState := crepRuntimeCallerState caller callee
                      match result with
                      | .normal => some (.error, callee)
                      | .returned values =>
                          match info with
                          | none =>
                              some (.returned values, clearCrepRuntimeLocals callerState)
                          | some (destinations, _) =>
                              match crepRuntimeAssignExisting
                                  caller.locals destinations values with
                              | some locals =>
                                  some (.normal, { callerState with locals := locals })
                              | none => some (.error, callee)
                      | .raised exception =>
                          match info with
                          | some (_, some (caught, continuation)) =>
                              if caught == exception then
                                evalCrepRuntimeProg handler primitive fuel
                                  { callerState with locals := caller.locals } continuation
                              else
                                some (.raised exception, clearCrepRuntimeLocals callerState)
                          | _ => some (.raised exception, clearCrepRuntimeLocals callerState)
                      | .broke _label => some (.error, callee)
                      | .continued _label => some (.error, callee)
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
            let nextState :=
              { state with locals := updateCrepRuntimeLocal state.locals name (.word value) }
            match evalCrepRuntimeProg handler primitive fuel nextState body with
            | none => none
            | some result => some (restoreCrepRuntimeStep name (state.locals name) result)
    | _fuel + 1, state, .assign name value =>
        match evalCrepRuntimeExp state value with
        | none => some (.error, state)
        | some value =>
            match state.locals name with
            | some _ =>
                some (.normal, { state with locals := updateCrepRuntimeLocal state.locals name (.word value) })
            | none => some (.error, state)
    | _fuel + 1, state, .primitive names operator arguments =>
        match arguments.mapM (fun name => (state.locals name).map panTheWord) with
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
            some (.normal, setCrepRuntimeGlobals address (.word value) state)
        | none => some (.error, state)
    | fuel + 1, state, .seq first second =>
        match evalCrepRuntimeProg handler primitive fuel state first with
        | none => none
        | some result =>
            let (result, state) := fixCrepRuntimeClock state result
            match result with
            | .normal =>
              match evalCrepRuntimeProg handler primitive fuel state second with
              | some result => some result
              | none => none
            | _ => some (result, state)
    | fuel + 1, state, .ite condition thenBranch elseBranch =>
        match evalCrepRuntimeExp state condition with
        | none => some (.error, state)
        | some conditionValue =>
            match evalCrepRuntimeProg handler primitive fuel state
              (if conditionValue != 0 then thenBranch else elseBranch) with
            | some result => some result
            | none => none
    | fuel + 1, state, .while condition body =>
        match evalCrepRuntimeExp state condition with
        | none => some (.error, state)
        | some conditionValue =>
            if conditionValue == 0 then
              some (.normal, state)
            else if state.clock = 0 then
              some (.timeout, clearCrepRuntimeLocals state)
            else
              let decremented := decCrepClock state
              match evalCrepRuntimeProg handler primitive fuel decremented body with
              | none => none
              | some result =>
                  let (result, state) := fixCrepRuntimeClock decremented result
                  match result with
                  | .normal =>
                    match evalCrepRuntimeProg handler primitive fuel state
                    (.while condition body) with
                    | some result => some result
                    | none => none
                  | .continued 0 =>
                    match evalCrepRuntimeProg handler primitive fuel state
                      (.while condition body) with
                    | some result => some result
                    | none => none
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

/-! General target Call exception-dispatch step.  `hcalleeBody` and
`hhandlerBody` are the recursive-evaluation induction hypotheses for the
callee and compiled handler continuation.  Callee code, argument values,
destinations, exception code, and both programs are arbitrary.  The statement
exposes `crepRuntimeCallerState` and the exact callee clock clamp, and assumes
no execution result for the enclosing Call. -/
theorem evalCrepRuntimeCall_handlesRaisedBody
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α) (fuel : Nat)
    (caller : CrepRuntimeState α σ)
    (destinations : List Nat) (caught exception : α)
    (continuation body : CrepProg α) (function : FunName)
    (arguments : List (CrepExp α)) (values : List α)
    (calleeLocals : Nat → Option (PanWordLab α))
    (calleeState : CrepRuntimeState α σ)
    (handlerResult : CrepRuntimeStep α σ ε)
    (harguments : evalCrepRuntimeExps caller arguments = some values)
    (hlookup : lookupCrepRuntimeCode function values caller.code =
      some (body, calleeLocals))
    (hinfoValid : crepRuntimeCallInfoValid
      (some (destinations, some (caught, continuation))) = true)
    (hclock : caller.clock ≠ 0)
    (hmatch : (caught == exception) = true)
    (hcalleeBody : evalCrepRuntimeProg handler primitive fuel
      (decCrepClock { caller with locals := calleeLocals }) body =
        some (.raised exception, calleeState))
    (hhandlerBody : evalCrepRuntimeProg handler primitive fuel
      { crepRuntimeCallerState caller calleeState with
        locals := caller.locals } continuation = some handlerResult) :
    evalCrepRuntimeCall handler primitive (fuel + 1) caller
      (some (destinations, some (caught, continuation))) function arguments =
        some handlerResult := by
  simp [evalCrepRuntimeCall, harguments, hlookup, hinfoValid, hclock,
    fixCrepRuntimeClock, hmatch, hcalleeBody, hhandlerBody]

/-! `evalCrepRuntimeResult` is fuel bounded: `none` means the supplied target
fuel was exhausted. Semantic `Error` is returned as `some (.error, state)`, so
correctness arguments can choose a sufficient fuel without treating a cutoff
as a program result. -/
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
    crepRuntimeLoad state address = some (panTheWord (state.memory address)) := by
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
