import Flapjack.HolRef
import Flapjack.Compiler.Backend.StackCarrier
import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Compiler.Backend.WordToStack

/-!
# Faithful Cake Word-to-Stack register-format helpers

Lean counterpart of the register-format helpers of
`cakeml/compiler/backend/word_to_stackScript.sml`, the Word-to-Stack pass of the
CakeML RISC-V backend.  This module ports `wReg1`, `wReg2`, `wRegWrite1`,
`wRegWrite2` and `format_var`, which the return/argument path of `comp` uses to
split a register number into the live frame-slot assignment, and eventually
feed the Word-to-Stack `compile_semantics` theorem
(`word_to_stackProofScript.sml:10709`).

`wReg1`/`wReg2`/`format_var` touch only `num`/`bool`/option/sum/list with no
word operation and no `dimindex (:'a)`, so their tags are unconditional.

`wRegWrite1`/`wRegWrite2` take `g : num -> stackLang$prog` and return a
`stackLang$prog`, and `stack_move`/`StackArgs`/`wMoveSingle`/`wMoveAux` likewise
produce `stackLang$prog`.  These are stated over the exact shared-word carrier
`Flapjack.Compiler.Backend.StackLang.ProgM α`, whose single type parameter is
the word type and whose FFI field is the faithful `MlString` (matching HOL's
opaque `mlstring`), so the conclusion carrier is exact and the definitions are
tagged.  The separate executable `StackCarrier.ProgW` uses Lean `String` in its
FFI field and is not used here. -/

namespace Flapjack.Compiler.Backend.WordToStackRegFormat

open Flapjack.Compiler.Backend.StackCarrier (ProgW)
open Flapjack.Compiler.Backend.StackLang (ProgM)

/-- Exact port of HOL `wReg1_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:28-31`):

```
wReg1 r (k,f,f') =
  let r = r DIV 2 in
    if r < k then ([],r) else ([(k,f-1 - (r - k))],k)
```

    Splits a register number into the live frame-slot assignment used by the
    return path.  Touches only `num`/`bool`/list, so it is word-independent and
    needs no width index; the exact tag is unconditional. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wReg1_def"]
def wReg1 (r : Nat) (kf : Nat × Nat × Nat) : List (Nat × Nat) × Nat :=
  let r := r / 2
  if r < kf.1 then ([], r) else ([(kf.1, kf.2.1 - 1 - (r - kf.1))], kf.1)

/-- Exact port of HOL `wReg2_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:34-37`):

```
wReg2 r (k,f,f') =
  let r = r DIV 2 in
    if r < k then ([],r) else ([(k+1,f-1 - (r - k))],k+1)
```

    As `wReg1` but biased to the `k+1` frame slot; word-independent and exactly
    tagged with no width index. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wReg2_def"]
def wReg2 (r : Nat) (kf : Nat × Nat × Nat) : List (Nat × Nat) × Nat :=
  let r := r / 2
  if r < kf.1 then ([], r) else ([(kf.1 + 1, kf.2.1 - 1 - (r - kf.1))], kf.1 + 1)

/-- Exact port of HOL `wRegWrite1_def`

```
wRegWrite1 g r (k,f,f') =
  let r = r DIV 2 in
    if r < k then g r else Seq (g k) (StackStore k (f-1 - (r - k)))
```

    Emits the program produced by `g` at the assigned register, spilling the
    frame variable with a `StackStore` when the register is above the live
    window.  Stated over the exact shared-word carrier `ProgM α`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wRegWrite1_def"]
def wRegWrite1 {α : Type} (g : Nat → ProgM α)
    (r : Nat) (kf : Nat × Nat × Nat) : ProgM α :=
  let r := r / 2
  if r < kf.1 then g r
  else .seq (g kf.1) (.stackStore kf.1 (kf.2.1 - 1 - (r - kf.1)))

/-- Exact port of HOL `wRegWrite2_def`

```
wRegWrite2 g r (k,f,f') =
  let r = r DIV 2 in
    if r < k then g r else Seq (g (k+1)) (StackStore (k+1) (f-1 - (r - k)))
```

    As `wRegWrite1` biased to the `k+1` frame slot, over the exact shared-word
    carrier `ProgM α`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wRegWrite2_def"]
def wRegWrite2 {α : Type} (g : Nat → ProgM α)
    (r : Nat) (kf : Nat × Nat × Nat) : ProgM α :=
  let r := r / 2
  if r < kf.1 then g r
  else .seq (g (kf.1 + 1)) (.stackStore (kf.1 + 1) (kf.2.1 - 1 - (r - kf.1)))

/-- Exact port of HOL `format_var_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:78-80`):

```
(format_var k NONE = INL (k+1)) /\
(format_var k (SOME x) = if x < k then INL x else INR x)
```

    Classifies a variable as a register (`INL`) or a frame slot (`INR`) relative
    to the live window `k`.  Pure `num`/`option`/sum, word-independent and
    exactly tagged with no width index. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "format_var_def"]
def formatVar (k : Nat) : Option Nat → Sum Nat Nat
  | none => .inl (k + 1)
  | some x => if x < k then .inl x else .inr x

/-- Exact port of HOL `stack_move_def`

```
(stack_move 0 start offset i p = p) /\
(stack_move (SUC n) start offset i p =
   Seq (stack_move n (start+1) offset i p)
       (Seq (StackLoad i (start+offset)) (StackStore i start)))
```

    Builds the `StackLoad`/`StackStore` chain that moves `n` argument slots,
    over the exact shared-word carrier `ProgM α`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "stack_move_def"]
def stackMove {α : Type} (n start offset i : Nat) (p : ProgM α) : ProgM α :=
  match n with
  | 0 => p
  | n + 1 =>
    .seq (stackMove n (start + 1) offset i p)
      (.seq (.stackLoad i (start + offset)) (.stackStore i start))

/-- Exact port of HOL `StackArgs_def`

```
StackArgs dest arg_count (k,f,f') =
  let n = stack_arg_count dest arg_count k in
    stack_move n 0 f k (StackAlloc n)
```

    Allocates the argument slots and moves the return/argument registers into
    them.  Uses the already-ported `stackArgCount` and `stackMove`, over the
    exact shared-word carrier `ProgM γ`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "StackArgs_def"]
def stackArgs {α β γ : Type} (dest : Sum α β) (argCount : Nat)
    (kf : Nat × Nat × Nat) : ProgM γ :=
  let n := Flapjack.Compiler.Backend.WordToStack.stackArgCount dest argCount kf.1
  stackMove n 0 kf.2.1 kf.1 (.stackAlloc n)

/-- Exact port of HOL `wMoveSingle_def`

```
wMoveSingle (x,y) (k,f,f') =
  case (x,y) of
  | (INL r1, INL r2) => Inst (Arith (Binop Or r1 r2 (Reg r2)))
  | (INL r1, INR r2) => StackLoad r1 (f-1 - (r2 - k))
  | (INR r1, INL r2) => StackStore r2 (f-1 - (r1 - k))
  | (INR r1, INR r2) => Seq (StackLoad k (f-1 - (r2 - k)))
                            (StackStore k (f-1 - (r1 - k)))
```

    Lowers one formatted move pair to the register-format `stackLang$prog`
    fragment, over the exact shared-word carrier `ProgM α`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wMoveSingle_def"]
def wMoveSingle {α : Type} (xy : Sum Nat Nat × Sum Nat Nat)
    (kf : Nat × Nat × Nat) : ProgM α :=
  match xy with
  | (.inl r1, .inl r2) => .inst (.arith (.binop .or r1 r2 (.reg r2)))
  | (.inl r1, .inr r2) => .stackLoad r1 (kf.2.1 - 1 - (r2 - kf.1))
  | (.inr r1, .inl r2) => .stackStore r2 (kf.2.1 - 1 - (r1 - kf.1))
  | (.inr r1, .inr r2) =>
    .seq (.stackLoad kf.1 (kf.2.1 - 1 - (r2 - kf.1)))
      (.stackStore kf.1 (kf.2.1 - 1 - (r1 - kf.1)))

/-- Exact port of HOL `wMoveAux_def`

```
(wMoveAux [] kf = Skip) /\
(wMoveAux [xy] kf = wMoveSingle xy kf) /\
(wMoveAux (xy::xys) kf = Seq (wMoveSingle xy kf) (wMoveAux xys kf))
```

    Sequences the register-format fragments of a list of formatted move pairs,
    over the exact shared-word carrier `ProgM α`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wMoveAux_def"]
def wMoveAux {α : Type} : List (Sum Nat Nat × Sum Nat Nat) → Nat × Nat × Nat → ProgM α
  | [], _ => .skip
  | [xy], kf => wMoveSingle xy kf
  | xy :: xys, kf => .seq (wMoveSingle xy kf) (wMoveAux xys kf)

/-- Exact port of HOL `copy_ret_aux_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:429-441`):

```
(copy_ret_aux k f n =
   if n = 0 then Skip
   else let n' = n-1 in
     list_Seq [StackLoad k n'; StackStore k (n'+f); copy_ret_aux k f n'])
```

    Copies `n` return slots from slot `k` down to slot `k+f`, as a
    `list_Seq` of load/store fragments over the exact shared-word carrier
    `ProgM α`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "copy_ret_aux_def"]
def copyRetAux {α : Type} (k f : Nat) : Nat → ProgM α
  | 0 => .skip
  | n + 1 =>
    Flapjack.Compiler.Backend.StackLang.listSeq
      [ .stackLoad k n, .stackStore k (n + f), copyRetAux k f n ]

/-- Exact port of HOL `copy_ret_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:443-451`):

```
copy_ret perf is_handle (k,f,f') vs kont =
  let n = num_stack_ret k vs in
  if n = 0 then kont
  else Seq (copy_ret_aux k (if is_handle then f + handler_slots perf else f) n)
           (SeqStackFree n kont)
```

    over the exact shared-word carrier `ProgM α`; `num_stack_ret`,
    `handler_slots` and `seq_stack_free` are the already-ported helpers.
    HOL is polymorphic in the return-value list: `num_stack_ret k vs` only
    measures `LENGTH vs`, so `vs : List β` is an INDEPENDENT carrier from the
    `ProgM α` carrier of `kont`, matching the exact HOL statement. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "copy_ret_def"]
def copyRet {α β : Type} (perf isHandle : Bool) (kf : Nat × Nat × Nat)
    (vs : List β) (kont : ProgM α) : ProgM α :=
  let n := Flapjack.Compiler.Backend.WordToStack.numStackRet kf.1 vs
  if n = 0 then kont
  else
    .seq
      (copyRetAux kf.1
        (if isHandle then kf.2.1 + Flapjack.Compiler.Backend.WordToStack.handlerSlots perf
         else kf.2.1)
        n)
      (Flapjack.Compiler.Backend.WordToStack.seqStackFree n kont)
/-- Structural analogue of HOL `wLive_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:252`):

```
wLive (live:cutsets) (bitmaps:'a word app_list # num) k f f' =
  if f = 0 then (Skip,bitmaps)
  else let (new_bitmaps,i) = insert_bitmap (write_bitmap (SND live) k f') bitmaps in
         (Seq (Inst (Const k (n2w (i+1)))) (StackStore k 0), new_bitmaps)
```

    NOT TAGGED: HOL consumes the live set as a `num_set` (`SND live`) through
    `toAList`/`MEM`; that `sptree` carrier is outside the CakeML submodule and is
    modelled here (as in `writeBitmapHOL`) by an order-insensitive key list.
    `live` below is that modelled domain.  The stackLang fragment
    `Seq`/`Inst`/`Const`/`StackStore` is stated over the exact shared-word
    carrier `Flapjack.Compiler.Backend.StackLang.ProgM`. -/
def wLiveW {width : Nat} [NeZero width]
    (live : List Nat) (bitmaps : Flapjack.AppList (BitVec width) × Nat)
    (k f f' : Nat) :
    ProgM (BitVec width) × (Flapjack.AppList (BitVec width) × Nat) :=
  if f = 0 then (.skip, bitmaps)
  else
    let inserted :=
      Flapjack.Compiler.Backend.WordToStack.insertBitmap
        (Flapjack.Compiler.Backend.WordToStack.writeBitmapHOL live k f') bitmaps
    (.seq (.inst (.const k (BitVec.ofNat width (inserted.2 + 1))))
      (.stackStore k 0), inserted.1)

/-- Exact port of HOL `StackHandlerArgs_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:350`):

```
StackHandlerArgs perf dest arg_count (k,f,f') =
  StackArgs dest arg_count (k, f + handler_slots perf, f' + handler_slots perf)
```

    `'a` is arbitrary in HOL (no word operation and no `dimindex (:'a)`), so the
    generic-`α` statement over the shared-word carrier `ProgM` is exact. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "StackHandlerArgs_def"]
def stackHandlerArgs {α : Type} (perf : Bool) (dest : Sum Nat Nat) (arg_count : Nat)
    (kf : Nat × Nat × Nat) : ProgM α :=
  stackArgs dest arg_count
    (kf.1,
     kf.2.1 + Flapjack.Compiler.Backend.WordToStack.handlerSlots perf,
     kf.2.2 + Flapjack.Compiler.Backend.WordToStack.handlerSlots perf)

/-- Exact port of HOL `PopHandler_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:378`):

```
PopHandler perf (k,f,f') prog =
  Seq (StackLoad k 2) (Seq (Set Handler k) (Seq (StackFree (handler_slots perf)) prog))
```

    `'a` is arbitrary in HOL, so the generic-`α` statement is exact. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "PopHandler_def"]
def popHandler {α : Type} (perf : Bool) (kf : Nat × Nat × Nat) (prog : ProgM α) : ProgM α :=
  .seq (.stackLoad kf.1 2)
    (.seq (.set .handler kf.1)
      (.seq (.stackFree (Flapjack.Compiler.Backend.WordToStack.handlerSlots perf)) prog))

/-- Exact port of HOL `PushHandler_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:355`):

```
PushHandler perf l1 l2 (k,f,f') =
  Seq (StackAlloc (handler_slots perf))
   (Seq (Inst (Const k 1w))
   (Seq (StackStore k 0)
   (Seq (LocValue k l1 l2)
   (Seq (StackStore k 1)
   (Seq (Get k Handler)
   (Seq (StackStore k 2)
   (Seq (if perf then
           list_Seq [ Inst (Arith (Binop Or k perf_rsp (Reg perf_rsp))) ;
                      StackStore k 3 ;
                      Inst (Arith (Binop Or k perf_rbp (Reg perf_rbp))) ;
                      StackStore k 4 ]
         else Skip)
   (Seq (StackGetSize k)
        (Set Handler k)))))))))
```

    HOL's `Const k 1w` is word-indexed (`'a word`), so the exact statement is
    the width-indexed `ProgM (BitVec width)` with `[NeZero width]`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "PushHandler_def"]
def pushHandlerW {width : Nat} [NeZero width]
    (perf : Bool) (l1 l2 : Nat) (kf : Nat × Nat × Nat) : ProgM (BitVec width) :=
  .seq (.stackAlloc (Flapjack.Compiler.Backend.WordToStack.handlerSlots perf))
    (.seq (.inst (.const kf.1 (1 : BitVec width)))
      (.seq (.stackStore kf.1 0)
        (.seq (.locValue kf.1 l1 l2)
          (.seq (.stackStore kf.1 1)
            (.seq (.get kf.1 .handler)
              (.seq (.stackStore kf.1 2)
                (.seq
                  (if perf then
                    Flapjack.Compiler.Backend.StackLang.listSeq
                      [ .inst (.arith (.binop .or kf.1
                          (Flapjack.Compiler.Backend.WordToStack.perfRsp)
                          (.reg (Flapjack.Compiler.Backend.WordToStack.perfRsp)))),
                        .stackStore kf.1 3,
                        .inst (.arith (.binop .or kf.1
                          (Flapjack.Compiler.Backend.WordToStack.perfRbp)
                          (.reg (Flapjack.Compiler.Backend.WordToStack.perfRbp)))),
                        .stackStore kf.1 4 ]
                  else .skip)
                  (.seq (.stackGetSize kf.1)
                        (.set .handler kf.1)))))))))

/-- HOL `word_to_stack$call_dest`: the destination register/stack slot of a
    call target.  A direct target is the `INL` position; an indirect target is
    taken from the last argument via `wReg2`, with the target load emitted by
    `wStackLoad`.  HOL is polymorphic in the stack program's word type, so the
    result is `ProgM α` for an arbitrary `α`; the argument list is `num list`
    because HOL's `LAST args` is fed to `wReg2 : num -> ...`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "call_dest_def"]
def callDest {α : Type} (pos : Option Nat) (args : List Nat)
    (kf : Nat × Nat × Nat) : ProgM α × Sum Nat Nat :=
  match pos with
  | some p => (.skip, .inl p)
  | none =>
    match args.getLast? with
    | none => (.skip, .inl Flapjack.raiseStubLocation)
    | some last =>
      let w := wReg2 last kf
      (Flapjack.Compiler.Backend.WordToStack.wStackLoad w.1 .skip, .inr w.2)

/-- HOL `word_to_stack$perf_call_prefix`
    (`cakeml/compiler/backend/word_to_stackScript.sml:319-334`): the performance
    frame-setup prefix.  It writes the return address with `LocValue`, stores the
    old frame pointers relative to `perf_rsp`, and then atomically commits the
    new frame before syncing `perf_rbp`.  The immediates are concrete words, so
    the port is width-indexed. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "perf_call_prefix_def"]
def perfCallPrefixW {width : Nat} [NeZero width]
    (l1 l2 k : Nat) : ProgM (BitVec width) :=
  Flapjack.Compiler.Backend.StackLang.listSeq
    [ .locValue k l1 l2,
      .inst (.mem .store k
        (.addr (Flapjack.Compiler.Backend.WordToStack.perfRsp)
          (-8 : BitVec width))),
      .inst (.mem .store (Flapjack.Compiler.Backend.WordToStack.perfRbp)
        (.addr (Flapjack.Compiler.Backend.WordToStack.perfRsp)
          (-16 : BitVec width))),
      .inst (.arith (.binop .sub (Flapjack.Compiler.Backend.WordToStack.perfRsp)
        (Flapjack.Compiler.Backend.WordToStack.perfRsp) (.imm (16 : BitVec width)))),
      .inst (.arith (.binop .or (Flapjack.Compiler.Backend.WordToStack.perfRbp)
        (Flapjack.Compiler.Backend.WordToStack.perfRsp)
        (.reg (Flapjack.Compiler.Backend.WordToStack.perfRsp)))) ]

/-- HOL `word_to_stack$perf_call_suffix`
    (`cakeml/compiler/backend/word_to_stackScript.sml:336-343`): pops the saved
    frame pointer and discards both frame slots in one atomic step.  Width-indexed
    because of the concrete `0w`/`16w` immediates. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "perf_call_suffix_def"]
def perfCallSuffixW {width : Nat} [NeZero width] : ProgM (BitVec width) :=
  Flapjack.Compiler.Backend.StackLang.listSeq
    [ .inst (.mem .load (Flapjack.Compiler.Backend.WordToStack.perfRbp)
        (.addr (Flapjack.Compiler.Backend.WordToStack.perfRsp) (0 : BitVec width))),
      .inst (.arith (.binop .add (Flapjack.Compiler.Backend.WordToStack.perfRsp)
        (Flapjack.Compiler.Backend.WordToStack.perfRsp) (.imm (16 : BitVec width)))) ]

/-- HOL `word_to_stack$raise_stub`
    (`cakeml/compiler/backend/word_to_stackScript.sml:557-576`): restores the
    handler and (when `perf`) the performance frame pointers from slots 3/4, then
    hands off to the next handler.  HOL is polymorphic in the word type and the
    body contains no word literal, so the port is generic in the carrier
    parameter `α`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "raise_stub_def"]
def raiseStub {α : Type} (perf : Bool) (k : Nat) : ProgM α :=
  .seq (.get k .handler)
    (.seq (.stackSetSize k)
      (.seq
        (if perf then
          Flapjack.Compiler.Backend.StackLang.listSeq
            [ .stackLoad k 3,
              .inst (.arith (.binop .or (Flapjack.Compiler.Backend.WordToStack.perfRsp)
                k (.reg k))),
              .stackLoad k 4,
              .inst (.arith (.binop .or (Flapjack.Compiler.Backend.WordToStack.perfRbp)
                k (.reg k))) ]
        else .skip)
        (.seq (.stackLoad k 2)
          (.seq (.set .handler k)
            (.seq (.stackLoad k 1)
              (.seq (.stackFree (Flapjack.Compiler.Backend.WordToStack.handlerSlots perf))
                (.raise k)))))))

/-- HOL `word_to_stack$store_consts_stub`
    (`cakeml/compiler/backend/word_to_stackScript.sml:578-580`): stores the
    constant pool and returns.  Word-independent, so generic in `α`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "store_consts_stub_def"]
def storeConstsStub {α : Type} (k : Nat) : ProgM α :=
  .seq (.storeConsts k (k + 1) none) (.ret 0)

/-- Exact port of HOL `wShareInst_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:186-224`):

```
(wShareInst Load   v (Addr ad offset) kf =
   let (l,n2) = wReg1 ad kf in
     wStackLoad l (wRegWrite1 (\r. ShMemOp Load r (Addr n2 offset)) v kf)) /\
  ... Load8/Load16/Load32 likewise ...
(wShareInst Store  v (Addr ad offset) kf =
   let (l1,n2) = wReg1 ad kf in
   let (l2,n1) = wReg2 v kf in
     wStackLoad (l1 ++ l2) (ShMemOp Store n1 (Addr n2 offset))) /\
  ... Store8/Store16/Store32 likewise ...
```

    Splits the shared-memory address register through `wReg1` (and, for stores,
    the stored value through `wReg2`), spilling through `wStackLoad`.  HOL is
    polymorphic in the stack word type `'a`, so this is generic in `α` over the
    exact shared-word carrier `ProgM α`. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wShareInst_def"]
def wShareInst {α : Type} (op : WordMemOp) (v : Nat)
    (address : WordLangAddr α) (kf : Nat × Nat × Nat) : ProgM α :=
  match op, address with
  | .load, .addr ad offset =>
      let l := wReg1 ad kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad l.1
        (wRegWrite1 (fun r => .shMemOp .load r (.addr l.2 offset)) v kf)
  | .load8, .addr ad offset =>
      let l := wReg1 ad kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad l.1
        (wRegWrite1 (fun r => .shMemOp .load8 r (.addr l.2 offset)) v kf)
  | .load16, .addr ad offset =>
      let l := wReg1 ad kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad l.1
        (wRegWrite1 (fun r => .shMemOp .load16 r (.addr l.2 offset)) v kf)
  | .load32, .addr ad offset =>
      let l := wReg1 ad kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad l.1
        (wRegWrite1 (fun r => .shMemOp .load32 r (.addr l.2 offset)) v kf)
  | .store, .addr ad offset =>
      let l1 := wReg1 ad kf
      let l2 := wReg2 v kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l1.1 ++ l2.1)
        (.shMemOp .store l2.2 (.addr l1.2 offset))
  | .store8, .addr ad offset =>
      let l1 := wReg1 ad kf
      let l2 := wReg2 v kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l1.1 ++ l2.1)
        (.shMemOp .store8 l2.2 (.addr l1.2 offset))
  | .store16, .addr ad offset =>
      let l1 := wReg1 ad kf
      let l2 := wReg2 v kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l1.1 ++ l2.1)
        (.shMemOp .store16 l2.2 (.addr l1.2 offset))
  | .store32, .addr ad offset =>
      let l1 := wReg1 ad kf
      let l2 := wReg2 v kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l1.1 ++ l2.1)
        (.shMemOp .store32 l2.2 (.addr l1.2 offset))

/-- Exact port of HOL `wInst_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:88-175`).

Every clause is mirrored, with `dimindex (:'a) = 64` becoming `width = 64`.
`Load16`/`Store16` are not handled by HOL and fall to the `Skip` catch-all, as
in the source. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wInst_def"]
def wInst {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (kf : Nat × Nat × Nat) : ProgM (BitVec width) :=
  match i with
  | .const n c =>
      wRegWrite1 (fun n => .inst (.const n c)) n kf
  | .arith (.binop bop n1 n2 (.imm imm)) =>
      let l := wReg1 n2 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad l.1
        (wRegWrite1 (fun n1 => .inst (.arith (.binop bop n1 l.2 (.imm imm)))) n1 kf)
  | .arith (.binop bop n1 n2 (.reg n3)) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l.1 ++ l'.1)
        (wRegWrite1 (fun n1 => .inst (.arith (.binop bop n1 l.2 (.reg l'.2)))) n1 kf)
  | .arith (.shift sh n1 n2 (.imm imm)) =>
      let l := wReg1 n2 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad l.1
        (wRegWrite1 (fun n1 => .inst (.arith (.shift sh n1 l.2 (.imm imm)))) n1 kf)
  | .arith (.shift sh n1 n2 (.reg n3)) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l.1 ++ l'.1)
        (wRegWrite1 (fun n1 => .inst (.arith (.shift sh n1 l.2 (.reg l'.2)))) n1 kf)
  | .arith (.div n1 n2 n3) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l.1 ++ l'.1)
        (wRegWrite1 (fun n1 => .inst (.arith (.div n1 l.2 l'.2))) n1 kf)
  | .arith (.addCarry n1 n2 n3 n4) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l.1 ++ l'.1)
        (wRegWrite1 (fun n1 => .inst (.arith (.addCarry n1 l.2 l'.2 n4))) n1 kf)
  | .arith (.addOverflow n1 n2 n3 n4) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l.1 ++ l'.1)
        (wRegWrite1 (fun n1 => .inst (.arith (.addOverflow n1 l.2 l'.2 n4))) n1 kf)
  | .arith (.subOverflow n1 n2 n3 n4) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l.1 ++ l'.1)
        (wRegWrite1 (fun n1 => .inst (.arith (.subOverflow n1 l.2 l'.2 n4))) n1 kf)
  | .arith (.longMul _ _ _ _) =>
      .inst (.arith (.longMul 3 0 0 2))
  | .arith (.longDiv _ _ _ _ n5) =>
      let l := wReg1 n5 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad l.1
        (.inst (.arith (.longDiv 0 3 3 0 l.2)))
  | .mem .load n1 (.addr n2 offset) =>
      let l := wReg1 n2 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad l.1
        (wRegWrite1 (fun n1 => .inst (.mem .load n1 (.addr l.2 offset))) n1 kf)
  | .mem .store n1 (.addr n2 offset) =>
      let l1 := wReg1 n2 kf
      let l2 := wReg2 n1 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l1.1 ++ l2.1)
        (.inst (.mem .store l2.2 (.addr l1.2 offset)))
  | .mem .load8 n1 (.addr n2 offset) =>
      let l := wReg1 n2 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad l.1
        (wRegWrite1 (fun n1 => .inst (.mem .load8 n1 (.addr l.2 offset))) n1 kf)
  | .mem .store8 n1 (.addr n2 offset) =>
      let l1 := wReg1 n2 kf
      let l2 := wReg2 n1 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l1.1 ++ l2.1)
        (.inst (.mem .store8 l2.2 (.addr l1.2 offset)))
  | .mem .load32 n1 (.addr n2 offset) =>
      let l := wReg1 n2 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad l.1
        (wRegWrite1 (fun n1 => .inst (.mem .load32 n1 (.addr l.2 offset))) n1 kf)
  | .mem .store32 n1 (.addr n2 offset) =>
      let l1 := wReg1 n2 kf
      let l2 := wReg2 n1 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l1.1 ++ l2.1)
        (.inst (.mem .store32 l2.2 (.addr l1.2 offset)))
  | .fp (.fpLess r f1 f2) =>
      wRegWrite1 (fun r => .inst (.fp (.fpLess r f1 f2))) r kf
  | .fp (.fpLessEqual r f1 f2) =>
      wRegWrite1 (fun r => .inst (.fp (.fpLessEqual r f1 f2))) r kf
  | .fp (.fpEqual r f1 f2) =>
      wRegWrite1 (fun r => .inst (.fp (.fpEqual r f1 f2))) r kf
  | .fp (.fpMovToReg r1 r2 d) =>
      if width = 64 then
        wRegWrite1 (fun r1 => .inst (.fp (.fpMovToReg r1 0 d))) r1 kf
      else
        wRegWrite2
          (fun r2 => wRegWrite1 (fun r1 => .inst (.fp (.fpMovToReg r1 r2 d))) r1 kf)
          r2 kf
  | .fp (.fpMovFromReg d r1 r2) =>
      let l := wReg1 r1 kf
      let l' := if width = 64 then ([], 0) else wReg2 r2 kf
      Flapjack.Compiler.Backend.WordToStack.wStackLoad (l.1 ++ l'.1)
        (.inst (.fp (.fpMovFromReg d l.2 l'.2)))
  | .fp f => .inst (.fp f)
  | _ => .inst .skip

end Flapjack.Compiler.Backend.WordToStackRegFormat
