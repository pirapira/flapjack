import Flapjack.HolRef
import Flapjack.Compiler.Backend.StackCarrier
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

`wReg1`/`wReg2`/`format_var` touch only `num`/`bool`/`option`/sum/list with no
word operation and no `dimindex (:'a)`, so their tags are unconditional.
`wRegWrite1`/`wRegWrite2` take `g : num -> stackLang$prog` and return a
`stackLang$prog`; they are polymorphic in the word type `'a`, and their exact
statements are over the canonical single-word-parameter carrier
`Flapjack.Compiler.Backend.StackCarrier.ProgW`. -/

namespace Flapjack.Compiler.Backend.WordToStackRegFormat

open Flapjack.Compiler.Backend.StackCarrier (ProgW)

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
    (`cakeml/compiler/backend/word_to_stackScript.sml:40-43`):

```
wRegWrite1 g r (k,f,f') =
  let r = r DIV 2 in
    if r < k then g r else Seq (g k) (StackStore k (f-1 - (r - k)))
```

    Emits the program produced by `g` at the assigned register, spilling the
    frame variable with a `StackStore` when the register is above the live
    window.  HOL is polymorphic in the word type `'a` (the emitted `Seq`/
    `StackStore` carry `num` fields only); the exact statement is over the
    canonical shared-word `ProgW` carrier, with `g : num -> stackLang$prog`
    returning a program directly. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wRegWrite1_def"]
def wRegWrite1 {α : Type} (g : Nat → ProgW α)
    (r : Nat) (kf : Nat × Nat × Nat) : ProgW α :=
  let r := r / 2
  if r < kf.1 then g r
  else .seq (g kf.1) (.stackStore kf.1 (kf.2.1 - 1 - (r - kf.1)))

/-- Exact port of HOL `wRegWrite2_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:46-49`):

```
wRegWrite2 g r (k,f,f') =
  let r = r DIV 2 in
    if r < k then g r else Seq (g (k+1)) (StackStore (k+1) (f-1 - (r - k)))
```

    As `wRegWrite1` biased to the `k+1` frame slot, over the canonical
    shared-word `ProgW` carrier. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wRegWrite2_def"]
def wRegWrite2 {α : Type} (g : Nat → ProgW α)
    (r : Nat) (kf : Nat × Nat × Nat) : ProgW α :=
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
    (`cakeml/compiler/backend/word_to_stackScript.sml:288-291`):

```
(stack_move 0 start offset i p = p) /\
(stack_move (SUC n) start offset i p =
   Seq (stack_move n (start+1) offset i p)
       (Seq (StackLoad i (start+offset)) (StackStore i start)))
```

    Builds the `StackLoad`/`StackStore` chain that moves `n` argument slots.
    HOL is polymorphic in the word type `'a`; only `Seq`/`StackLoad`/`StackStore`
    (num fields) are used, so the exact statement is over the canonical
    shared-word `ProgW` carrier. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "stack_move_def"]
def stackMove {α : Type} (n start offset i : Nat) (p : ProgW α) : ProgW α :=
  match n with
  | 0 => p
  | n + 1 =>
    .seq (stackMove n (start + 1) offset i p)
      (.seq (.stackLoad i (start + offset)) (.stackStore i start))

/-- Exact port of HOL `StackArgs_def`
    (`cakeml/compiler/backend/word_to_stackScript.sml:293-297`):

```
StackArgs dest arg_count (k,f,f') =
  let n = stack_arg_count dest arg_count k in
    stack_move n 0 f k (StackAlloc n)
```

    Allocates the argument slots and moves the return/argument registers into
    them.  Uses the already-ported `stackArgCount` and `stackMove`; HOL is
    polymorphic in the word type `'a`, so the exact statement is over the
    canonical shared-word `ProgW` carrier. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "StackArgs_def"]
def stackArgs {α β γ : Type} (dest : Sum α β) (argCount : Nat)
    (kf : Nat × Nat × Nat) : ProgW γ :=
  let n := Flapjack.Compiler.Backend.WordToStack.stackArgCount dest argCount kf.1
  stackMove n 0 kf.2.1 kf.1 (.stackAlloc n)

end Flapjack.Compiler.Backend.WordToStackRegFormat
