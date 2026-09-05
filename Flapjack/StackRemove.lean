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
  stackRemoveJoin
    (.const config.addressScratch (stackStorePosition store))
    (.arith .add config.addressScratch config.storeBase config.addressScratch)

def stackRemoveGet (config : StackRemoveConfig) (destination : Nat)
    (store : StackStore) : StackProg α :=
  match store with
  | .currHeap => .arith .or destination config.currHeap config.currHeap
  | _ =>
      stackRemoveJoin (stackRemoveAddress config store)
        (.inst (.mem .load destination config.addressScratch))

def stackRemoveSet (config : StackRemoveConfig) (store : StackStore)
    (source : Nat) : StackProg α :=
  match store with
  | .currHeap => .arith .or config.currHeap source source
  | _ =>
      stackRemoveJoin (stackRemoveAddress config store)
        (.inst (.mem .store source config.addressScratch))

def stackRemoveFuel : Nat → StackRemoveConfig → StackProg α → StackProg α
  | 0, _, program => program
  | fuel + 1, _, .skip => .skip
  | fuel + 1, config, .get destination store =>
      stackRemoveGet config destination store
  | fuel + 1, config, .set store source =>
      stackRemoveSet config store source
  | fuel + 1, _, .inst instruction => .inst instruction
  | fuel + 1, _, .shMem operator source address =>
      .shMem operator source address
  | fuel + 1, _, .const destination value => .const destination value
  | fuel + 1, _, .arith operator destination left right =>
      .arith operator destination left right
  | fuel + 1, _, .shift operator destination left right =>
      .shift operator destination left right
  | fuel + 1, _, .opCurrHeap operator destination source =>
      .opCurrHeap operator destination source
  | fuel + 1, config, .call returnHandler target handler =>
      match returnHandler, handler with
      | none, none => .call none target none
      | some (program, link, returnLabel, entryLabel), none =>
          .call (some (stackRemoveFuel fuel config program, link, returnLabel, entryLabel))
            target none
      | none, some (program, exceptionLabel, handlerLabel) =>
          .call none target
            (some (stackRemoveFuel fuel config program, exceptionLabel, handlerLabel))
      | some (returnProgram, link, returnLabel, entryLabel),
          some (handlerProgram, exceptionLabel, handlerLabel) =>
          .call
            (some (stackRemoveFuel fuel config returnProgram, link, returnLabel, entryLabel))
            target
            (some (stackRemoveFuel fuel config handlerProgram, exceptionLabel, handlerLabel))
  | fuel + 1, config, .seq first second =>
      .seq (stackRemoveFuel fuel config first) (stackRemoveFuel fuel config second)
  | fuel + 1, config, .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right (stackRemoveFuel fuel config thenBranch)
        (stackRemoveFuel fuel config elseBranch)
  | fuel + 1, config, .loop body => .loop (stackRemoveFuel fuel config body)
  | fuel + 1, _, .jumpLower register target label =>
      .jumpLower register target label
  | fuel + 1, _, .alloc words => .alloc words
  | fuel + 1, _, .storeConsts source bitmap stub =>
      .storeConsts source bitmap stub
  | fuel + 1, _, .raise exception => .raise exception
  | fuel + 1, _, .return value => .return value
  | fuel + 1, _, .break label => .break label
  | fuel + 1, _, .continue label => .continue label
  | fuel + 1, _, .ffi function configuration configurationLength array arrayLength
      returnAddress =>
      .ffi function configuration configurationLength array arrayLength returnAddress
  | fuel + 1, _, .tick => .tick
  | fuel + 1, _, .locValue destination label entry =>
      .locValue destination label entry
  | fuel + 1, _, .install codeBuffer codeLength dataBuffer dataLength returnAddress =>
      .install codeBuffer codeLength dataBuffer dataLength returnAddress
  | fuel + 1, _, .rawCall target => .rawCall target
  | fuel + 1, _, .stackAlloc words => .stackAlloc words
  | fuel + 1, _, .stackFree words => .stackFree words
  | fuel + 1, _, .stackStore register offset => .stackStore register offset
  | fuel + 1, _, .stackStoreAny register offsetRegister =>
      .stackStoreAny register offsetRegister
  | fuel + 1, _, .stackLoad register offset => .stackLoad register offset
  | fuel + 1, _, .stackLoadAny register offsetRegister =>
      .stackLoadAny register offsetRegister
  | fuel + 1, _, .stackGetSize register => .stackGetSize register
  | fuel + 1, _, .stackSetSize register => .stackSetSize register
  | fuel + 1, _, .bitmapLoad destination address => .bitmapLoad destination address
  | fuel + 1, _, .halt register => .halt register

/- A generous default keeps the public pass total and executable.  The worker
   is exposed so callers processing generated programs can choose a larger
   bound; a structural size measure can replace this bound when the complete
   CakeML pass is ported. -/
def stackRemove (config : StackRemoveConfig) (program : StackProg α) : StackProg α :=
  stackRemoveFuel 1024 config program

theorem stackRemove_get_currHeap (config : StackRemoveConfig) (destination : Nat) :
    stackRemove config (.get destination .currHeap : StackProg α) =
      .arith .or destination config.currHeap config.currHeap := by
  simp [stackRemove, stackRemoveFuel, stackRemoveGet]

theorem stackRemove_set_currHeap (config : StackRemoveConfig) (source : Nat) :
    stackRemove config (.set .currHeap source : StackProg α) =
      .arith .or config.currHeap source source := by
  simp [stackRemove, stackRemoveFuel, stackRemoveSet]

end Flapjack
