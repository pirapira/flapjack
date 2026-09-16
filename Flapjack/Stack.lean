import Flapjack.Word

/-!
# StackLang

The StackLang layer is the first stack-based intermediate representation in
CakeML's backend. It is deliberately kept separate from the RISC-V model:
StackLang still has structured control flow and an explicit handler stack, while
the later stack-to-lab pass is responsible for flattening these operations.

This file ports the call, exception, and FFI carriers from
`cakeml/compiler/backend/stackLangScript.sml` and the corresponding boundary
equations from `word_to_stackScript.sml`. Register allocation and the complete
word-to-stack compiler remain subsequent stages.
-/

namespace Flapjack

inductive StackStore where
  | nextFree
  | endOfHeap
  | triggerGC
  | heapLength
  | progStart
  | bitmapBase
  | currHeap
  | otherHeap
  | allocSize
  | globals
  | globReal
  | handler
  | genStart
  | codeBuffer
  | codeBufferEnd
  | bitmapBuffer
  | bitmapBufferEnd
  | temp (index : Nat)
  deriving DecidableEq, Repr

inductive StackCallTarget where
  | label (name : Nat)
  | register (name : Nat)
  deriving DecidableEq, Repr

inductive StackProg (α : Type u) where
  | skip
  | const (destination value : Nat)
  | inst (instruction : WordInst)
  | shMem (operator : WordMemOp) (source address : Nat)
  | get (destination : Nat) (store : StackStore)
  | set (store : StackStore) (source : Nat)
  | arith (operator : BinOp) (destination left right : Nat)
  | shift (operator : Shift) (destination left right : Nat)
  | opCurrHeap (operator : BinOp) (destination source : Nat)
  | call (returnHandler : Option (StackProg α × Nat × Nat × Nat))
      (target : StackCallTarget) (handler : Option (StackProg α × Nat × Nat))
  | seq (first second : StackProg α)
  | ite (operator : Cmp) (condition : Nat) (right : WordRegImm α)
      (thenBranch elseBranch : StackProg α)
  | loop (body : StackProg α)
  | jumpLower (register target : Nat) (label : Nat)
  | alloc (words : Nat)
  | storeConsts (source bitmap : Nat) (stub : Option Nat)
  | codeBufferWrite (address value : Nat)
  | dataBufferWrite (address value : Nat)
  | raise (exception : Nat)
  | return (value : Nat)
  | break (label : Nat)
  | continue (label : Nat)
  | ffi (function : FunName) (configuration configurationLength array arrayLength : Nat)
      (returnAddress : Nat)
  | tick
  | locValue (destination label entry : Nat)
  | install (codeBuffer codeLength dataBuffer dataLength returnAddress : Nat)
  | rawCall (target : Nat)
  | stackAlloc (words : Nat)
  | stackFree (words : Nat)
  | stackStore (register offset : Nat)
  | stackStoreAny (register offsetRegister : Nat)
  | stackLoad (register offset : Nat)
  | stackLoadAny (register offsetRegister : Nat)
  | stackGetSize (register : Nat)
  | stackSetSize (register : Nat)
  | bitmapLoad (destination address : Nat)
  | halt (register : Nat)
  deriving Repr

/-! Register relabeling is kept at the StackLang boundary so a source-shaped
    Cake program can be converted to the port's hardware-numbered Lab input
    without changing stores, offsets, labels, or constants. -/
def stackMapWordArith (map : Nat → Nat) : WordArith → WordArith
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      .longMul (map destinationLeft) (map destinationRight)
        (map sourceLeft) (map sourceRight)
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      .longDiv (map destinationLeft) (map destinationRight)
        (map sourceLeft) (map sourceRight) (map quotient)
  | .addCarry destination resultCarry sourceLeft sourceRight carryIn =>
      .addCarry (map destination) (map resultCarry) (map sourceLeft)
        (map sourceRight) (map carryIn)
  | .cakeAddCarry destination sourceLeft sourceRight carry =>
      .cakeAddCarry (map destination) (map sourceLeft) (map sourceRight)
        (map carry)
  | .div destination dividend divisor =>
      .div (map destination) (map dividend) (map divisor)
  | .binOp operator destination sourceLeft sourceRight =>
      .binOp operator (map destination) (map sourceLeft) (map sourceRight)

def stackMapWordInst (map : Nat → Nat) : WordInst → WordInst
  | .arith operation => .arith (stackMapWordArith map operation)
  | .mem operator destination address =>
      .mem operator (map destination) (map address)

def stackMapWordRegImm (map : Nat → Nat) : WordRegImm α → WordRegImm α
  | .imm value => .imm value
  | .reg register => .reg (map register)

def stackMapCallTarget (map : Nat → Nat) : StackCallTarget → StackCallTarget
  | .label label => .label label
  | .register register => .register (map register)

def stackMapDepth : StackProg α → Nat
  | .call returnHandler _ handler =>
      1 + max
        (match returnHandler with
        | none => 0
        | some (program, _, _, _) => stackMapDepth program)
        (match handler with
        | none => 0
        | some (program, _, _) => stackMapDepth program)
  | .seq first second => 1 + max (stackMapDepth first) (stackMapDepth second)
  | .ite _ _ _ thenBranch elseBranch =>
      1 + max (stackMapDepth thenBranch) (stackMapDepth elseBranch)
  | .loop body => 1 + stackMapDepth body
  | _ => 1
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def stackMapRegisters (map : Nat → Nat) : StackProg α → StackProg α
  | .skip => .skip
  | .const destination value => .const (map destination) value
  | .inst instruction => .inst (stackMapWordInst map instruction)
  | .shMem operator source address => .shMem operator (map source) (map address)
  | .get destination store => .get (map destination) store
  | .set store source => .set store (map source)
  | .arith operator destination left right =>
      .arith operator (map destination) (map left) (map right)
  | .shift operator destination left right =>
      .shift operator (map destination) (map left) (map right)
  | .opCurrHeap operator destination source =>
      .opCurrHeap operator (map destination) (map source)
  | .call none target none => .call none (stackMapCallTarget map target) none
  | .call none target (some (program, exceptionLabel, handlerLabel)) =>
      .call none (stackMapCallTarget map target)
        (some (stackMapRegisters map program, exceptionLabel, handlerLabel))
  | .call (some (program, link, returnLabel, entryLabel)) target none =>
      .call (some (stackMapRegisters map program, link, returnLabel, entryLabel))
        (stackMapCallTarget map target) none
  | .call (some (program, link, returnLabel, entryLabel)) target
      (some (handlerProgram, exceptionLabel, handlerLabel)) =>
      .call (some (stackMapRegisters map program, link, returnLabel, entryLabel))
        (stackMapCallTarget map target)
        (some (stackMapRegisters map handlerProgram, exceptionLabel, handlerLabel))
  | .seq first second => .seq (stackMapRegisters map first) (stackMapRegisters map second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator (map condition) (stackMapWordRegImm map right)
        (stackMapRegisters map thenBranch) (stackMapRegisters map elseBranch)
  | .loop body => .loop (stackMapRegisters map body)
  | .jumpLower register target label => .jumpLower (map register) (map target) label
  | .alloc words => .alloc words
  | .storeConsts source bitmap stub => .storeConsts (map source) (map bitmap) (stub.map map)
  | .codeBufferWrite address value => .codeBufferWrite (map address) (map value)
  | .dataBufferWrite address value => .dataBufferWrite (map address) (map value)
  | .raise exception => .raise (map exception)
  | .return value => .return (map value)
  | .break label => .break label
  | .continue label => .continue label
  | .ffi function configuration configurationLength array arrayLength returnAddress =>
      .ffi function (map configuration) configurationLength (map array) arrayLength
        (map returnAddress)
  | .tick => .tick
  | .locValue destination label entry => .locValue (map destination) label entry
  | .install codeBuffer codeLength dataBuffer dataLength returnAddress =>
      .install (map codeBuffer) codeLength (map dataBuffer) dataLength
        (map returnAddress)
  | .rawCall target => .rawCall (map target)
  | .stackAlloc words => .stackAlloc words
  | .stackFree words => .stackFree words
  | .stackStore register offset => .stackStore (map register) offset
  | .stackStoreAny register offsetRegister => .stackStoreAny (map register) (map offsetRegister)
  | .stackLoad register offset => .stackLoad (map register) offset
  | .stackLoadAny register offsetRegister => .stackLoadAny (map register) (map offsetRegister)
  | .stackGetSize register => .stackGetSize (map register)
  | .stackSetSize register => .stackSetSize (map register)
  | .bitmapLoad destination address => .bitmapLoad (map destination) (map address)
  | .halt register => .halt (map register)
termination_by program => stackMapDepth program
decreasing_by
  all_goals simp [stackMapDepth] <;> omega

def stackSeq : List (StackProg α) → StackProg α
  | [] => .skip
  | [program] => program
  | program :: programs => .seq program (stackSeq programs)

def stackHandlerSlots (perf : Bool) : Nat :=
  if perf then 5 else 3

def stackPerfRsp : Nat := 14

def stackPerfRbp : Nat := 15

/- The CakeML stack argument move copies the stack-resident arguments into a
   fresh frame. `scratch` is the register used for the load/store pair. -/
def stackMove : Nat → Nat → Nat → Nat → StackProg α → StackProg α
  | 0, _, _, _, program => program
  | count + 1, start, offset, scratch, program =>
      .seq (stackMove count (start + 1) offset scratch program)
        (.seq (.stackLoad scratch (start + offset))
          (.stackStore scratch start))

def stackArgs (count frameOffset scratch : Nat) : StackProg α :=
  stackMove count 0 frameOffset scratch (.stackAlloc count)

def stackHandlerArgs (perf : Bool) (count frameOffset scratch : Nat) : StackProg α :=
  stackArgs count (frameOffset + stackHandlerSlots perf) scratch

/- The handler record layout follows `PushHandler_def` in CakeML:
   slot 0 = handler entry marker, slot 1 = handler PC, slot 2 = previous
   handler, and (in perf mode) slots 3 and 4 preserve stack/frame pointers. -/
def stackPushHandler (perf : Bool) (handlerLabel exceptionLabel register : Nat) :
    StackProg α :=
  stackSeq [
    .stackAlloc (stackHandlerSlots perf),
    .const register 1,
    .stackStore register 0,
    .locValue register handlerLabel exceptionLabel,
    .stackStore register 1,
    .get register .handler,
    .stackStore register 2,
    (if perf then
      stackSeq [
        .arith .or register stackPerfRsp stackPerfRsp,
        .stackStore register 3,
        .arith .or register stackPerfRbp stackPerfRbp,
        .stackStore register 4
      ]
    else .skip),
    .stackGetSize register,
    .set .handler register
  ]

def stackPopHandler (perf : Bool) (register : Nat) (program : StackProg α) :
    StackProg α :=
  stackSeq [
    .stackLoad register 2,
    .set .handler register,
    .stackFree (stackHandlerSlots perf),
    program
  ]

/-! The callee-return part of CakeML's Word-to-Stack calling convention.

    `num_stack_ret` counts values that were returned in the caller's stack
    frame rather than in the first `k` ABI result registers.  `copy_ret_aux`
    copies the stack-resident suffix from the old frame into the current one,
    starting at its highest slot just as CakeML's recursive definition does.
    Keeping these as StackLang carriers makes the convention available before
    the complete allocator supplies concrete frame sizes. -/
def stackNumReturnSlots (k : Nat) (values : List Nat) : Nat :=
  values.length + 1 - k

def stackCopyReturnAux (register frameOffset : Nat) : Nat → StackProg α
  | 0 => .skip
  | count + 1 =>
      stackSeq [
        .stackLoad register count,
        .stackStore register (count + frameOffset),
        stackCopyReturnAux register frameOffset count
      ]

def stackFreeIfNonzero (count : Nat) (program : StackProg α) : StackProg α :=
  if count = 0 then program else .seq (.stackFree count) program

def stackCopyReturn (perf isHandler : Bool) (k register frameOffset : Nat)
    (values : List Nat) (continuation : StackProg α) : StackProg α :=
  let count := stackNumReturnSlots k values
  if count = 0 then
    continuation
  else
    .seq (stackCopyReturnAux register
      (if isHandler then frameOffset + stackHandlerSlots perf else frameOffset) count)
      (stackFreeIfNonzero count continuation)

def stackRaiseStub (perf : Bool) (register : Nat) : StackProg α :=
  stackSeq [
    .get register .handler,
    .stackSetSize register,
    (if perf then
      stackSeq [
        .stackLoad register 3,
        .arith .or register stackPerfRsp register,
        .stackLoad register 4,
        .arith .or register stackPerfRbp register
      ]
    else .skip),
    .stackLoad register 2,
    .set .handler register,
    .stackLoad register 1,
    .stackFree (stackHandlerSlots perf),
    .raise register
  ]

/- The HOL development reserves the final stub location for the raise entry.
   The concrete target table will fill this in when stack-to-lab is ported. -/
def stackRaiseStubLocation : Nat := 0

/- The first three section labels are reserved by the executable Flapjack
   runtime-linked entry point: raise, StoreConsts, and the collector. -/
def stackStoreConstsStubLocation : Nat := 1

def stackGcStubLocation : Nat := 2

def stackFunctionFirstLabel : Nat := 3

def wordToStackFfi (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    StackProg α :=
  .ffi function configuration configurationLength array arrayLength 0

def wordToStackRaise (_exception : Nat) : StackProg α :=
  .call none (.label stackRaiseStubLocation) none

def wordToStackCallNoHandler (_perf : Bool) (target : Nat)
    (argumentCount frameOffset scratch : Nat)
    (returnValues : List Nat) (returnCode : StackProg α)
    (returnLabel entryLabel : Nat) : StackProg α :=
  let callCode :=
    .call (some (returnCode, 0, returnLabel, entryLabel)) (.label target) none
  stackSeq [
    stackArgs (argumentCount + 1) frameOffset scratch,
    callCode,
    .stackFree (returnValues.length)
  ]

def wordToStackCallWithHandlerInSection (perf : Bool) (target : Nat)
    (argumentCount frameOffset scratch : Nat)
    (returnCode handlerCode : StackProg α)
    (returnLabel entryLabel handlerLabel handlerEntryLabel exceptionLabel : Nat) : StackProg α :=
  let returnCode := stackPopHandler perf scratch returnCode
  let callCode :=
    .call (some (returnCode, 0, returnLabel, entryLabel)) (.label target)
      (some (handlerCode, exceptionLabel, handlerEntryLabel))
  stackSeq [
    stackPushHandler perf handlerEntryLabel handlerLabel scratch,
    stackHandlerArgs perf (argumentCount + 1) frameOffset scratch,
    callCode
  ]

/-! Source-shaped variant of the handler call boundary.  Cake's argument count
    includes the return destination, while only arguments beyond the Word
    register window need a fresh stack frame. -/
def wordToStackCallWithHandlerInSectionAtRegisterCount (perf : Bool) (target : Nat)
    (argumentCount registerCount frameOffset scratch : Nat)
    (returnCode handlerCode : StackProg α)
    (returnLabel entryLabel handlerLabel handlerEntryLabel exceptionLabel : Nat) :
    StackProg α :=
  let returnCode := stackPopHandler perf scratch returnCode
  let callCode :=
    .call (some (returnCode, 0, returnLabel, entryLabel)) (.label target)
      (some (handlerCode, exceptionLabel, handlerEntryLabel))
  let stackArgumentCount := argumentCount + 1 - registerCount
  stackSeq [
    stackPushHandler perf handlerEntryLabel handlerLabel scratch,
    stackHandlerArgs perf stackArgumentCount frameOffset scratch,
    callCode
  ]

def wordToStackCallWithHandler (perf : Bool) (target : Nat)
    (argumentCount frameOffset scratch : Nat)
    (returnCode handlerCode : StackProg α)
    (returnLabel entryLabel handlerLabel exceptionLabel : Nat) : StackProg α :=
  let callCode :=
    .call (some (returnCode, 0, returnLabel, entryLabel)) (.label target)
      (some (handlerCode, exceptionLabel, handlerLabel))
  stackSeq [
    stackPushHandler perf handlerLabel exceptionLabel scratch,
    stackHandlerArgs perf (argumentCount + 1) frameOffset scratch,
    callCode
  ]

/-! CakeML's `call_dest` accepts either a code label (`INL`) or a computed
    register (`INR`, an indirect call).  These two carriers are the same as the
    labelled versions above but keep the computed target instead of fixing a
    label, which is how the original lowers an indirect call. -/
def wordToStackCallNoHandlerTarget (_perf : Bool) (target : StackCallTarget)
    (argumentCount frameOffset scratch : Nat)
    (returnValues : List Nat) (returnCode : StackProg α)
    (returnLabel entryLabel : Nat) : StackProg α :=
  let callCode :=
    .call (some (returnCode, 0, returnLabel, entryLabel)) target none
  stackSeq [
    stackArgs (argumentCount + 1) frameOffset scratch,
    callCode,
    .stackFree (returnValues.length)
  ]

def wordToStackCallWithHandlerInSectionTarget (perf : Bool) (target : StackCallTarget)
    (argumentCount frameOffset scratch : Nat)
    (returnCode handlerCode : StackProg α)
    (returnLabel entryLabel handlerLabel handlerEntryLabel exceptionLabel : Nat) : StackProg α :=
  let returnCode := stackPopHandler perf scratch returnCode
  let callCode :=
    .call (some (returnCode, 0, returnLabel, entryLabel)) target
      (some (handlerCode, exceptionLabel, handlerLabel))
  stackSeq [
    stackPushHandler perf handlerLabel handlerEntryLabel scratch,
    stackHandlerArgs perf (argumentCount + 1) frameOffset scratch,
    callCode
  ]

theorem stackSeq_single (program : StackProg α) :
    stackSeq [program] = program := by
  rfl

theorem wordToStackFfi_shape (α : Type u) (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    wordToStackFfi (α := α) function configuration configurationLength array arrayLength =
      .ffi function configuration configurationLength array arrayLength 0 := by
  rfl

theorem wordToStackRaise_shape (α : Type u) (exception : Nat) :
    wordToStackRaise (α := α) exception =
      .call none (.label stackRaiseStubLocation) none := by
  rfl

end Flapjack
