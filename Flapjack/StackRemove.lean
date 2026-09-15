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

/- When `offsetImm` is supplied, store accesses lower to Cake's single
    `Mem … (Addr (k+1) (store_offset name))` form: one immediate-offset
    instruction from `storeBase`.  Without it, the address is materialized
    into `addressScratch` first. -/
def stackRemoveGet (config : StackRemoveConfig) (offsetImm : Option (Nat → α))
    (destination : Nat) (store : StackStore) : StackProg α :=
  match store with
  | .currHeap => stackRemoveMove destination config.currHeap
  | _ =>
      match offsetImm with
      | some imm =>
          .inst (.memOffset .load destination config.storeBase
            (imm (config.bytesInWord * stackStorePosition store)))
      | none =>
          stackRemoveJoin (stackRemoveAddress config store)
            (.inst (.mem .load destination config.addressScratch))

def stackRemoveSet (config : StackRemoveConfig) (offsetImm : Option (Nat → α))
    (store : StackStore) (source : Nat) : StackProg α :=
  match store with
  | .currHeap => stackRemoveMove config.currHeap source
  | _ =>
      match offsetImm with
      | some imm =>
          .inst (.memOffset .store source config.storeBase
            (imm (config.bytesInWord * stackStorePosition store)))
      | none =>
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

def stackRemoveStackLoad (config : StackRemoveConfig) (register offset : Nat) :
    StackProg α :=
  stackRemoveJoin (stackRemoveStackAddress config offset)
    (.inst (.mem .load register config.addressScratch))

def stackRemoveStackStore (config : StackRemoveConfig) (register offset : Nat) :
    StackProg α :=
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

def stackRemoveStackGetSize (config : StackRemoveConfig) (register : Nat) :
    StackProg α :=
  let shiftRegister :=
    if register = config.scratch then config.addressScratch else config.scratch
  stackRemoveJoin (stackRemoveMove register config.stackPointer)
    (stackRemoveJoin
      (.arith .sub register register config.stackBase)
      (stackRemoveJoin
        (.const shiftRegister config.wordShift)
        (.shift .lsr register register shiftRegister)))

def stackRemoveStackSetSize (config : StackRemoveConfig) (register : Nat) :
    StackProg α :=
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
    (offsetImm : Option (Nat → α)) (destination address : Nat) : StackProg α :=
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
    (offsetImm : Option (Nat → α)) (source bitmap : Nat) (_stub : Option Nat) :
    StackProg α :=
  stackRemoveJoin (stackRemoveGet config offsetImm bitmap .bitmapBase)
    (stackRemoveJoin (.const config.scratch 1)
      (stackRemoveJoin (.arith .add bitmap bitmap config.scratch)
        (stackRemoveJoin (.const config.scratch config.wordShift)
          (stackRemoveJoin (.shift .lsl bitmap bitmap config.scratch)
            (stackRemoveJoin (stackRemoveCopyLoop config source bitmap)
              (stackRemoveJoin (stackRemoveMove source 1)
                (stackRemoveMove bitmap 1)))))))

def stackRemoveFuel [OfNat α 0] [OfNat α 1] :
    Nat → StackRemoveConfig → Option (Nat → α) → StackProg α → StackProg α
  | 0, _, _, program => program
  | _fuel + 1, _, _, .skip => .skip
  | _fuel + 1, config, offsetImm, .get destination store =>
      stackRemoveGet config offsetImm destination store
  | _fuel + 1, config, offsetImm, .set store source =>
      stackRemoveSet config offsetImm store source
  | _fuel + 1, _, _, .inst instruction => .inst instruction
  | _fuel + 1, _, _, .shMem operator source address =>
      .shMem operator source address
  | _fuel + 1, _, _, .const destination value => .const destination value
  | _fuel + 1, _, _, .arith operator destination left right =>
      .arith operator destination left right
  | _fuel + 1, _, _, .shift operator destination left right =>
      .shift operator destination left right
  | _fuel + 1, config, _offsetImm, .opCurrHeap operator destination source =>
      stackRemoveOpCurrHeap config operator destination source
  | fuel + 1, config, offsetImm, .call returnHandler target handler =>
      match returnHandler, handler with
      | none, none => .call none target none
      | some (program, link, returnLabel, entryLabel), none =>
          .call (some (stackRemoveFuel fuel config offsetImm program, link, returnLabel, entryLabel))
            target none
      | none, some (program, exceptionLabel, handlerLabel) =>
          .call none target
            (some (stackRemoveFuel fuel config offsetImm program, exceptionLabel, handlerLabel))
      | some (returnProgram, link, returnLabel, entryLabel),
          some (handlerProgram, exceptionLabel, handlerLabel) =>
          .call
            (some (stackRemoveFuel fuel config offsetImm returnProgram, link, returnLabel, entryLabel))
            target
            (some (stackRemoveFuel fuel config offsetImm handlerProgram, exceptionLabel, handlerLabel))
  | fuel + 1, config, offsetImm, .seq first second =>
      .seq (stackRemoveFuel fuel config offsetImm first) (stackRemoveFuel fuel config offsetImm second)
  | fuel + 1, config, offsetImm, .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right (stackRemoveFuel fuel config offsetImm thenBranch)
        (stackRemoveFuel fuel config offsetImm elseBranch)
  | fuel + 1, config, offsetImm, .loop body => .loop (stackRemoveFuel fuel config offsetImm body)
  | _fuel + 1, _, _, .jumpLower register target label =>
      .jumpLower register target label
  | _fuel + 1, _, _, .alloc words => .alloc words
  | _fuel + 1, config, offsetImm, .storeConsts source bitmap stub =>
      stackRemoveStoreConsts config offsetImm source bitmap stub
  | _fuel + 1, _, _, .codeBufferWrite address value =>
      .codeBufferWrite address value
  | _fuel + 1, _, _, .dataBufferWrite address value =>
      .inst (.mem .store value address)
  | _fuel + 1, _, _, .raise exception => .raise exception
  | _fuel + 1, _, _, .return value => .return value
  | _fuel + 1, _, _, .break label => .break label
  | _fuel + 1, _, _, .continue label => .continue label
  | _fuel + 1, _, _, .ffi function configuration configurationLength array arrayLength
      returnAddress =>
      .ffi function configuration configurationLength array arrayLength returnAddress
  | _fuel + 1, _, _, .tick => .tick
  | _fuel + 1, _, _, .locValue destination label entry =>
      .locValue destination label entry
  | _fuel + 1, _, _, .install codeBuffer codeLength dataBuffer dataLength returnAddress =>
      .install codeBuffer codeLength dataBuffer dataLength returnAddress
  | _fuel + 1, _, _, .rawCall target => .rawCall target
  | _fuel + 1, config, _offsetImm, .stackAlloc words =>
      stackRemoveStackAlloc config words
  | _fuel + 1, config, _offsetImm, .stackFree words =>
      stackRemoveStackFree config words
  | _fuel + 1, config, _offsetImm, .stackStore register offset =>
      stackRemoveStackStore config register offset
  | _fuel + 1, config, _offsetImm, .stackStoreAny register offsetRegister =>
      stackRemoveStackStoreAny config register offsetRegister
  | _fuel + 1, config, _offsetImm, .stackLoad register offset =>
      stackRemoveStackLoad config register offset
  | _fuel + 1, config, offsetImm, .stackLoadAny register offsetRegister =>
      stackRemoveStackLoadAny config register offsetRegister
  | _fuel + 1, config, offsetImm, .stackGetSize register =>
      stackRemoveStackGetSize config register
  | _fuel + 1, config, offsetImm, .stackSetSize register =>
      stackRemoveStackSetSize config register
  | _fuel + 1, config, offsetImm, .bitmapLoad destination address =>
      stackRemoveBitmapLoad config offsetImm destination address
  | _fuel + 1, _, _, .halt register => .halt register

/- A generous default keeps the public pass total and executable.  The worker
   is exposed so callers processing generated programs can choose a larger
   bound; a structural size measure can replace this bound when the complete
   CakeML pass is ported. -/
def stackRemove [OfNat α 0] [OfNat α 1] (config : StackRemoveConfig)
    (program : StackProg α) : StackProg α :=
  stackRemoveFuel 1024 config none program

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
    (program : StackProg α) (offsetImm : Option (Nat → α) := none) :
    StackProg α :=
  stackRemoveFuel (stackProgDepth program) config offsetImm program

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
