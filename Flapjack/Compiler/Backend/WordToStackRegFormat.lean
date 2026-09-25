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

end Flapjack.Compiler.Backend.WordToStackRegFormat
