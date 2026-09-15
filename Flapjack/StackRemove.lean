import Flapjack.Stack

/-!
# StackLang store removal

This is the first slice of CakeML's `stack_remove` pass.  It resolves the
logical StackLang store interface into explicit word-memory accesses while
leaving the stack-frame operations for the next slice.  The pass is kept
target-neutral: the store base and scratch registers are supplied by the
caller, and the later LabLang/RISC-V passes decide how those instructions are
encoded.
-/

namespace Flapjack

structure StackRemoveConfig where
  storeBase : Nat
  currHeap : Nat
  scratch : Nat
  addressScratch : Nat
  stackPointer : Nat
  bytesInWord : Nat
  stackBase : Nat
  wordShift : Nat
  /- Cake's checked stack allocation emits JumpLower after allocation. -/
  jump : Bool := false
  deriving Repr

/- The order is the 1-based order of CakeML's `store_list`. -/
def stackStorePosition : StackStore → Nat
  | .nextFree => 1
  | .endOfHeap => 2
  | .heapLength => 3
  | .otherHeap => 4
  | .triggerGC => 5
  | .allocSize => 6
  | .handler => 7
  | .globals => 8
  | .globReal => 9
  | .progStart => 10
  | .bitmapBase => 11
  | .genStart => 12
  | .codeBuffer => 13
  | .codeBufferEnd => 14
  | .bitmapBuffer => 15
  | .bitmapBufferEnd => 16
  | .temp index => 17 + index
  | .currHeap => 0

def stackRemoveJoin (first second : StackProg α) : StackProg α :=
  match first, second with
  | .skip, second => second
  | first, .skip => first
  | first, second => .seq first second

def stackRemoveAddress (config : StackRemoveConfig) (store : StackStore) :
    StackProg α :=
  /- CakeML's store array grows down from `storeBase`: `store_offset` is the
     negated byte offset of the 1-based store position. -/
  stackRemoveJoin
    (.const config.addressScratch
      (config.bytesInWord * stackStorePosition store))
    (.arith .sub config.addressScratch config.storeBase config.addressScratch)

def stackRemoveMove (destination source : Nat) :
    StackProg α :=
  if destination = source then .skip
  else .arith .or destination source source

def stackRemoveGet (config : StackRemoveConfig) (destination : Nat)
    (store : StackStore) : StackProg α :=
  match store with
  | .currHeap => stackRemoveMove destination config.currHeap
  | _ =>
      stackRemoveJoin (stackRemoveAddress config store)
        (.inst (.mem .load destination config.addressScratch))

def stackRemoveSet (config : StackRemoveConfig) (store : StackStore)
    (source : Nat) : StackProg α :=
  match store with
  | .currHeap => stackRemoveMove config.currHeap source
  | _ =>
      stackRemoveJoin (stackRemoveAddress config store)
        (.inst (.mem .store source config.addressScratch))

def stackRemoveStackAddress (config : StackRemoveConfig) (offset : Nat) :
    StackProg α :=
  stackRemoveJoin
    (.const config.addressScratch (config.bytesInWord * offset))
    (.arith .add config.addressScratch config.stackPointer config.addressScratch)

def stackRemoveStackDelta (config : StackRemoveConfig) (operator : BinOp)
    (words : Nat) : StackProg α :=
  if words = 0 then
    .skip
  else if words ≤ 255 then
    stackRemoveJoin
      (.const config.scratch (config.bytesInWord * words))
      (.arith operator config.stackPointer config.stackPointer config.scratch)
  else
    stackRemoveJoin
      (stackRemoveStackDelta config operator 255)
      (stackRemoveStackDelta config operator (words - 255))
termination_by words
decreasing_by
  · omega
  · apply Nat.sub_lt <;> omega

def stackRemoveStackAlloc (config : StackRemoveConfig) (words : Nat) : StackProg α :=
  let delta := stackRemoveStackDelta config .sub words
  if words = 0 then
    .skip
  else if config.jump then
    stackRemoveJoin delta (.jumpLower config.stackPointer config.stackBase 2)
  else
      stackRemoveJoin delta
      (.ite .lower config.stackPointer (.reg config.stackBase)
        (.seq (.const 10 2) (.halt 10)) .skip)

def stackRemoveStackFree (config : StackRemoveConfig) (words : Nat) : StackProg α :=
  stackRemoveStackDelta config .add words

def stackRemoveStackLoad (config : StackRemoveConfig) (slotImm : Option (Nat → α))
    (register offset : Nat) : StackProg α :=
  match slotImm with
  | some imm =>
      .inst (.memOffset .load register config.stackPointer
        (imm (config.bytesInWord * offset)))
  | none =>
      stackRemoveJoin (stackRemoveStackAddress config offset)
        (.inst (.mem .load register config.addressScratch))

def stackRemoveStackStore (config : StackRemoveConfig) (slotImm : Option (Nat → α))
    (register offset : Nat) : StackProg α :=
  match slotImm with
  | some imm =>
      .inst (.memOffset .store register config.stackPointer
        (imm (config.bytesInWord * offset)))
  | none =>
      stackRemoveJoin (stackRemoveMove config.scratch register)
        (stackRemoveJoin (stackRemoveStackAddress config offset)
          (.inst (.mem .store config.scratch config.addressScratch)))

def stackRemoveStackLoadAny (config : StackRemoveConfig)
    (register offsetRegister : Nat) : StackProg α :=
  stackRemoveJoin
    (.arith .add config.addressScratch config.stackPointer offsetRegister)
    (.inst (.mem .load register config.addressScratch))

def stackRemoveStackStoreAny (config : StackRemoveConfig)
    (register offsetRegister : Nat) : StackProg α :=
  stackRemoveJoin (stackRemoveMove config.scratch register)
    (stackRemoveJoin
      (.arith .add config.addressScratch config.stackPointer offsetRegister)
      (.inst (.mem .store config.scratch config.addressScratch)))

def stackRemoveOpCurrHeap (config : StackRemoveConfig) (operator : BinOp)
    (destination source : Nat) : StackProg α :=
  .arith operator destination source config.currHeap

def stackRemoveStackGetSize (config : StackRemoveConfig)
    (shiftImm : Option (Nat → α)) (register : Nat) : StackProg α :=
  match shiftImm with
  | some imm =>
      stackRemoveJoin (stackRemoveMove register config.stackPointer)
        (stackRemoveJoin (.arith .sub register register config.stackBase)
          (.inst (.shiftInst .lsr register register (.imm (imm config.wordShift)))))
  | none =>
      let shiftRegister :=
        if register = config.scratch then config.addressScratch else config.scratch
      stackRemoveJoin (stackRemoveMove register config.stackPointer)
        (stackRemoveJoin
          (.arith .sub register register config.stackBase)
          (stackRemoveJoin
            (.const shiftRegister config.wordShift)
            (.shift .lsr register register shiftRegister)))

def stackRemoveStackSetSize (config : StackRemoveConfig)
    (shiftImm : Option (Nat → α)) (register : Nat) : StackProg α :=
  match shiftImm with
  | some imm =>
      stackRemoveJoin
        (.inst (.shiftInst .lsl register register (.imm (imm config.wordShift))))
        (stackRemoveJoin
          (.arith .or config.stackPointer config.stackBase config.stackBase)
          (.arith .add config.stackPointer config.stackPointer register))
  | none =>
      let shiftRegister :=
        if register = config.scratch then config.addressScratch else config.scratch
      stackRemoveJoin
        (.const shiftRegister config.wordShift)
        (stackRemoveJoin
          (.shift .lsl register register shiftRegister)
          (stackRemoveJoin
            (.arith .or config.stackPointer config.stackBase config.stackBase)
            (.arith .add config.stackPointer config.stackPointer register)))

def stackRemoveBitmapLoad (config : StackRemoveConfig)
    (offsetImm : Option (Nat → α)) (shiftImm : Option (Nat → α))
    (destination address : Nat) : StackProg α :=
  match shiftImm with
  | some imm =>
      stackRemoveJoin (stackRemoveGet config offsetImm destination .bitmapBase)
        (stackRemoveJoin
          (.arith .add destination destination address)
          (stackRemoveJoin
            (.inst (.shiftInst .lsl destination destination
              (.imm (imm config.wordShift))))
            (.inst (.mem .load destination destination))))
  | none =>
      stackRemoveJoin (stackRemoveGet config offsetImm destination .bitmapBase)
        (stackRemoveJoin
          (.arith .add destination destination address)
          (stackRemoveJoin
            (.const config.scratch config.wordShift)
            (stackRemoveJoin
              (.shift .lsl destination destination config.scratch)
              (.inst (.mem .load destination destination)))))

/-! `StoreConsts` copies the read-only constant area selected by a bitmap into
    the data buffer.  The HOL pass expresses the copy as two nested `While`s;
    StackLang represents those as a loop containing a conditional break. -/
def stackRemoveCopyEach [OfNat α 0] [OfNat α 1] (config : StackRemoveConfig)
    (source bitmap : Nat) : StackProg α :=
  let copyWord : StackProg α :=
    .seq (.inst (.mem .load source bitmap))
      (.seq (.arith .add bitmap bitmap config.scratch)
        (.seq (.ite .test 1 (.imm (1 : α)) .skip
            (.arith .add source source 3))
          (.seq (.shift .lsr 1 1 config.addressScratch)
            (.seq (.inst (.mem .store source 2))
              (.arith .add 2 2 config.scratch)))))
  .seq (.const config.scratch config.bytesInWord)
    (.seq (.const config.addressScratch 1)
      (.loop (.ite .notEqual 1 (.imm (1 : α)) copyWord (.break 0))))

def stackRemoveCopyLoop [OfNat α 0] [OfNat α 1] (config : StackRemoveConfig)
    (source bitmap : Nat) : StackProg α :=
  let copyEach := stackRemoveCopyEach config source bitmap
  let copyBitmapWord :=
    .seq copyEach
      (.seq (.inst (.mem .load 1 bitmap))
        (.arith .add bitmap bitmap config.scratch))
  .seq (.inst (.mem .load 1 bitmap))
    (.seq (.arith .add bitmap bitmap config.scratch)
      (.seq
        (.loop (.ite .less 1 (.imm (0 : α)) copyBitmapWord (.break 0)))
        copyEach))

def stackRemoveStoreConsts [OfNat α 0] [OfNat α 1] (config : StackRemoveConfig)
    (offsetImm : Option (Nat → α)) (shiftImm : Option (Nat → α))
    (source bitmap : Nat) (_stub : Option Nat) :
    StackProg α :=
  let shiftCode : StackProg α :=
    match shiftImm with
    | some imm =>
        .inst (.shiftInst .lsl bitmap bitmap (.imm (imm config.wordShift)))
    | none =>
        .seq (.const config.scratch config.wordShift)
          (.shift .lsl bitmap bitmap config.scratch)
  stackRemoveJoin (stackRemoveGet config offsetImm bitmap .bitmapBase)
    (stackRemoveJoin (.const config.scratch 1)
      (stackRemoveJoin (.arith .add bitmap bitmap config.scratch)
        (stackRemoveJoin shiftCode
          (stackRemoveJoin (stackRemoveCopyLoop config source bitmap)
            (stackRemoveJoin (stackRemoveMove source 1)
              (stackRemoveMove bitmap 1))))))

def stackRemoveFuel [OfNat α 0] [OfNat α 1] :
    Nat → StackRemoveConfig → Option (Nat → α) → Option (Nat → α) →
      Option (Nat → α) → StackProg α → StackProg α
  | 0, _, _, _, _, program => program
  | _fuel + 1, _, _, _, _, .skip => .skip
  | _fuel + 1, config, offsetImm, _slotImm, _shiftImm, .get destination store =>
      stackRemoveGet config offsetImm destination store
  | _fuel + 1, config, offsetImm, _slotImm, _shiftImm, .set store source =>
      stackRemoveSet config offsetImm store source
  | _fuel + 1, _, _, _, _, .inst instruction => .inst instruction
  | _fuel + 1, _, _, _, _, .shMem operator source address =>
      .shMem operator source address
  | _fuel + 1, _, _, _, _, .const destination value => .const destination value
  | _fuel + 1, _, _, _, _, .arith operator destination left right =>
      .arith operator destination left right
  | _fuel + 1, _, _, _, _, .shift operator destination left right =>
      .shift operator destination left right
  | _fuel + 1, config, _offsetImm, _slotImm, _shiftImm, .opCurrHeap operator destination source =>
      stackRemoveOpCurrHeap config operator destination source
  | fuel + 1, config, offsetImm, slotImm, shiftImm, .call returnHandler target handler =>
      match returnHandler, handler with
      | none, none => .call none target none
      | some (program, link, returnLabel, entryLabel), none =>
          .call (some (stackRemoveFuel fuel config offsetImm slotImm shiftImm program, link, returnLabel, entryLabel))
            target none
      | none, some (program, exceptionLabel, handlerLabel) =>
          .call none target
            (some (stackRemoveFuel fuel config offsetImm slotImm shiftImm program, exceptionLabel, handlerLabel))
      | some (returnProgram, link, returnLabel, entryLabel),
          some (handlerProgram, exceptionLabel, handlerLabel) =>
          .call
            (some (stackRemoveFuel fuel config offsetImm slotImm shiftImm returnProgram, link, returnLabel, entryLabel))
            target
            (some (stackRemoveFuel fuel config offsetImm slotImm shiftImm handlerProgram, exceptionLabel, handlerLabel))
  | fuel + 1, config, offsetImm, slotImm, shiftImm, .seq first second =>
      .seq (stackRemoveFuel fuel config offsetImm slotImm shiftImm first) (stackRemoveFuel fuel config offsetImm slotImm shiftImm second)
  | fuel + 1, config, offsetImm, slotImm, shiftImm, .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right (stackRemoveFuel fuel config offsetImm slotImm shiftImm thenBranch)
        (stackRemoveFuel fuel config offsetImm slotImm shiftImm elseBranch)
  | fuel + 1, config, offsetImm, slotImm, shiftImm, .loop body => .loop (stackRemoveFuel fuel config offsetImm slotImm shiftImm body)
  | _fuel + 1, _, _, _, _, .jumpLower register target label =>
      .jumpLower register target label
  | _fuel + 1, _, _, _, _, .alloc words => .alloc words
  | _fuel + 1, config, offsetImm, _slotImm, shiftImm, .storeConsts source bitmap stub =>
      stackRemoveStoreConsts config offsetImm shiftImm source bitmap stub
  | _fuel + 1, _, _, _, _, .codeBufferWrite address value =>
      .codeBufferWrite address value
  | _fuel + 1, _, _, _, _, .dataBufferWrite address value =>
      .inst (.mem .store value address)
  | _fuel + 1, _, _, _, _, .raise exception => .raise exception
  | _fuel + 1, _, _, _, _, .return value => .return value
  | _fuel + 1, _, _, _, _, .break label => .break label
  | _fuel + 1, _, _, _, _, .continue label => .continue label
  | _fuel + 1, _, _, _, _, .ffi function configuration configurationLength array arrayLength
      returnAddress =>
      .ffi function configuration configurationLength array arrayLength returnAddress
  | _fuel + 1, _, _, _, _, .tick => .tick
  | _fuel + 1, _, _, _, _, .locValue destination label entry =>
      .locValue destination label entry
  | _fuel + 1, _, _, _, _, .install codeBuffer codeLength dataBuffer dataLength returnAddress =>
      .install codeBuffer codeLength dataBuffer dataLength returnAddress
  | _fuel + 1, _, _, _, _, .rawCall target => .rawCall target
  | _fuel + 1, config, _offsetImm, _slotImm, _shiftImm, .stackAlloc words =>
      stackRemoveStackAlloc config words
  | _fuel + 1, config, _offsetImm, _slotImm, _shiftImm, .stackFree words =>
      stackRemoveStackFree config words
  | _fuel + 1, config, _offsetImm, slotImm, _shiftImm, .stackStore register offset =>
      stackRemoveStackStore config slotImm register offset
  | _fuel + 1, config, _offsetImm, _slotImm, _shiftImm, .stackStoreAny register offsetRegister =>
      stackRemoveStackStoreAny config register offsetRegister
  | _fuel + 1, config, _offsetImm, slotImm, _shiftImm, .stackLoad register offset =>
      stackRemoveStackLoad config slotImm register offset
  | _fuel + 1, config, _offsetImm, _slotImm, _shiftImm, .stackLoadAny register offsetRegister =>
      stackRemoveStackLoadAny config register offsetRegister
  | _fuel + 1, config, _offsetImm, _slotImm, shiftImm, .stackGetSize register =>
      stackRemoveStackGetSize config shiftImm register
  | _fuel + 1, config, _offsetImm, _slotImm, shiftImm, .stackSetSize register =>
      stackRemoveStackSetSize config shiftImm register
  | _fuel + 1, config, offsetImm, _slotImm, shiftImm, .bitmapLoad destination address =>
      stackRemoveBitmapLoad config offsetImm shiftImm destination address
  | _fuel + 1, _, _, _, _, .halt register => .halt register

/- A generous default keeps the public pass total and executable.  The worker
   is exposed so callers processing generated programs can choose a larger
   bound; a structural size measure can replace this bound when the complete
   CakeML pass is ported. -/
def stackRemove [OfNat α 0] [OfNat α 1] (config : StackRemoveConfig)
    (program : StackProg α) : StackProg α :=
  stackRemoveFuel 1024 config none none none program

def stackProgDepth : StackProg α → Nat
  | .call returnHandler _ handler =>
      1 + max
        (match returnHandler with
        | none => 0
        | some (program, _, _, _) => stackProgDepth program)
        (match handler with
        | none => 0
        | some (program, _, _) => stackProgDepth program)
  | .seq first second => 1 + max (stackProgDepth first) (stackProgDepth second)
  | .ite _ _ _ thenBranch elseBranch =>
      1 + max (stackProgDepth thenBranch) (stackProgDepth elseBranch)
  | .loop body => 1 + stackProgDepth body
  | _ => 1
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! A size-derived entry point for generated programs.  Every recursive child
    passed to `stackRemoveFuel` is structurally smaller than its parent, so
    `stackProgDepth program` supplies enough fuel for the maximum nesting depth
    without imposing a fixed limit on the source program. -/
def stackRemoveComplete [OfNat α 0] [OfNat α 1] (config : StackRemoveConfig)
    (program : StackProg α) (offsetImm : Option (Nat → α) := none)
    (slotImm : Option (Nat → α) := none)
    (shiftImm : Option (Nat → α) := none) : StackProg α :=
  stackRemoveFuel (stackProgDepth program) config offsetImm slotImm shiftImm program

theorem stackRemove_get_currHeap [OfNat α 0] [OfNat α 1]
    (config : StackRemoveConfig) (destination : Nat) :
    stackRemove config (.get destination .currHeap : StackProg α) =
      stackRemoveMove destination config.currHeap := by
  simp [stackRemove, stackRemoveFuel, stackRemoveGet]

theorem stackRemove_set_currHeap [OfNat α 0] [OfNat α 1]
    (config : StackRemoveConfig) (source : Nat) :
    stackRemove config (.set .currHeap source : StackProg α) =
      stackRemoveMove config.currHeap source := by
  simp [stackRemove, stackRemoveFuel, stackRemoveSet]

end Flapjack
