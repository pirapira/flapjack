import Flapjack.Compiler.Backend.WordToStack
import Flapjack.Compiler.Backend.WordToStackRegFormat
import Flapjack.RiscV.CakeAllocatorCore
import Flapjack.RiscV.CakeAllocatorBitsBridge

/-!
# Word-to-Stack `bits_to_word` parity

Parity fixture for `Flapjack.Compiler.Backend.WordToStack.bitsToWordW`, the
width-indexed faithful counterpart of HOL `bits_to_word_def`
(`cakeml/compiler/backend/word_to_stackScript.sml:225`) tagged in bead
`flapjack-pxn.18.5.15.3.1`.

The expected rows are the direct HOL `EVAL` results checked in at
`scripts/hol-probes/word_to_stack_bits_to_word_probe.out` (oracle checkout
`flapjack2`, `word_to_stackTheory` prebuilt):

```
bits_empty=0w  bits_true=1w  bits_false=0w
bits_true_false_true=5w  bits_all_true_3=7w  bits_pattern=18w
```

The last example ties the faithful word result back to the untagged executable
`Flapjack.RiscV.CakeAlloc.bitsToWord` for the in-range case.
-/

namespace Flapjack.Test.WordToStackBitsParity

open Flapjack.Compiler.Backend.WordToStack

def parityGuard : Bool :=
  (bitsToWordW (width := 64) ([] : List Bool) == 0) &&
  (bitsToWordW (width := 64) [true] == 1) &&
  (bitsToWordW (width := 64) [false] == 0) &&
  (bitsToWordW (width := 64) [true, false, true] == 5) &&
  (bitsToWordW (width := 64) [true, true, true] == 7) &&
  (bitsToWordW (width := 64) [false, true, false, false, true] == 18)

#eval parityGuard
#guard parityGuard

example : bitsToWordW (width := 64) [true, false, true] = (5 : BitVec 64) := by decide

example : (bitsToWordW (width := 8) [true, false, true]).toNat =
    Flapjack.RiscV.CakeAlloc.bitsToWord [true, false, true] := by decide

/-! ## `word_list` parity

Rows for the width-indexed `wordListW`, tagged against HOL `word_list_def`
(`cakeml/compiler/backend/word_to_stackScript.sml:231`; bead
`flapjack-pxn.18.5.15.3.2`), from
`scripts/hol-probes/word_to_stack_word_list_probe.out`:

```
wl_empty_d3=[0w]  wl_empty_d0=[0w]  wl_d0=[5w]
wl_short=[5w]  wl_split=[5w; 3w]  wl_twostep=[7w; 7w; 1w]
```
-/

def wordListParityGuard : Bool :=
  (wordListW (width := 64) ([] : List Bool) 3 == [0]) &&
  (wordListW (width := 64) ([] : List Bool) 0 == [0]) &&
  (wordListW (width := 64) [true, false, true] 0 == [5]) &&
  (wordListW (width := 64) [true, false, true] 5 == [5]) &&
  (wordListW (width := 64) [true, false, true, true] 2 == [5, 3]) &&
  (wordListW (width := 64) [true, true, true, true, true] 2 == [7, 7, 1])

#eval wordListParityGuard
#guard wordListParityGuard

example : wordListW (width := 64) [true, false, true, true] 2 =
    ([5, 3] : List (BitVec 64)) := by decide +kernel
/-! ## `chunk_to_bits` parity

Rows for the width-indexed `chunkToBitsW`, tagged against HOL
`chunk_to_bits_def` (`cakeml/compiler/backend/word_to_stackScript.sml:386`;
bead `flapjack-pxn.18.5.15.3.3`), from
`scripts/hol-probes/word_to_stack_chunk_to_bits_probe.out`:

```
cb_empty=1w  cb_single_true=3w  cb_single_false=2w
cb_true_false=5w  cb_false_true=6w  cb_three=11w  cb_ignores_word=T
```
-/

def chunkToBitsParityGuard : Bool :=
  (chunkToBitsW (width := 64) ([] : List (Bool × BitVec 64)) == 1) &&
  (chunkToBitsW (width := 64) [(true, 0)] == 3) &&
  (chunkToBitsW (width := 64) [(false, 0)] == 2) &&
  (chunkToBitsW (width := 64) [(true, 0), (false, 0)] == 5) &&
  (chunkToBitsW (width := 64) [(false, 0), (true, 0)] == 6) &&
  (chunkToBitsW (width := 64) [(true, 0), (true, 0), (false, 0)] == 11)

#eval chunkToBitsParityGuard
#guard chunkToBitsParityGuard

example : chunkToBitsW (width := 64) [(true, (0 : BitVec 64)), (false, 9)] =
    chunkToBitsW (width := 64) [(true, 0), (false, 0)] := by decide

/-! ## `chunk_to_bitmap` / `const_words_to_bitmap` parity

Rows for the width-indexed `chunkToBitmapW` and `constWordsToBitmapW`, tagged
against HOL `chunk_to_bitmap_def` / `const_words_to_bitmap_def`
(`cakeml/compiler/backend/word_to_stackScript.sml:393,397`; bead
`flapjack-pxn.18.5.15.3.4`), from
`scripts/hol-probes/word_to_stack_chunk_to_bitmap_probe.out`:

```
cbm_empty=[1w]  cbm_two=[5w; 0w; 9w]  cbm_payload=[3w; 7w]
cwb_empty=[1w]  cwb_short=[5w; 0w; 9w]
cwb_boundary8=[213w; 1w; 2w; 3w; 4w; 5w; 6w; 7w; 1w]
cwb_split8=[213w; 1w; 2w; 3w; 4w; 5w; 6w; 7w; 2w; 8w]
```

`cwb_boundary8` exercises `word8` (`dimindex (:'a) = 8`) with
`ws_len = dimindex-1 = 7`: HOL's strict `<` still recurses, splitting off the
first seven words and appending `chunk_to_bitmap [] = [1w]`.
-/

def chunkToBitmapParityGuard : Bool :=
  (chunkToBitmapW (width := 64) ([] : List (Bool × BitVec 64)) == [1]) &&
  (chunkToBitmapW (width := 64) [(true, 0), (false, 9)] == [5, 0, 9]) &&
  (chunkToBitmapW (width := 64) [(true, 7)] == [3, 7]) &&
  (constWordsToBitmapW (width := 64) ([] : List (Bool × BitVec 64)) 0 == [1]) &&
  (constWordsToBitmapW (width := 64) [(true, 0), (false, 9)] 2 == [5, 0, 9]) &&
  (constWordsToBitmapW (width := 8)
      [(true, 1), (false, 2), (true, 3), (false, 4), (true, 5), (false, 6), (true, 7)] 7
      == [213, 1, 2, 3, 4, 5, 6, 7, 1]) &&
  (constWordsToBitmapW (width := 8)
      [(true, 1), (false, 2), (true, 3), (false, 4), (true, 5), (false, 6), (true, 7), (false, 8)] 8
      == [213, 1, 2, 3, 4, 5, 6, 7, 2, 8])

#eval chunkToBitmapParityGuard
#guard chunkToBitmapParityGuard

example : constWordsToBitmapW (width := 8)
    [(true, 1), (false, 2), (true, 3), (false, 4), (true, 5), (false, 6), (true, 7), (false, 8)] 8 =
    ([213, 1, 2, 3, 4, 5, 6, 7, 2, 8] : List (BitVec 8)) := by decide +kernel

/-! ## `write_bitmap` oracle parity (untagged model)

`writeBitmapHOL` models HOL `write_bitmap_def`
(`cakeml/compiler/backend/word_to_stackScript.sml:240`) at the domain level and
is deliberately **not** tagged: HOL's `live` is a `num_set` (`unit spt`) whose
finite-map/`toAList` carrier lives outside the CakeML tree, so the faithful
observation is the `writeBitmapHOL_domain_insensitive` theorem rather than a
matching declaration (see `docs/NUM-SET-AUDIT.md`).  Rows from the direct HOL
`EVAL` probe `scripts/hol-probes/word_to_stack_write_bitmap_probe.out`:

```
wb_empty=[16w]  wb_single=[24w]  wb_two=[24w]  wb_offset=[240w; 2w]
wb_boundary=[0xE000000000000000w; 3w]
wb_order_a=[192w; 3w]  wb_order_b=[192w; 3w]  wb_order_eq=T
```
-/

def writeBitmapParityGuard : Bool :=
  (writeBitmapHOL (width := 8) ([] : List Nat) 0 4 == [16]) &&
  (writeBitmapHOL (width := 8) [0] 0 4 == [24]) &&
  (writeBitmapHOL (width := 8) [0, 1] 0 4 == [24]) &&
  (writeBitmapHOL (width := 8) [2, 4, 6] 0 8 == [240, 2]) &&
  (writeBitmapHOL (width := 64) [0, 2, 4] 0 64 == [(0xE000000000000000 : BitVec 64), 3]) &&
  (writeBitmapHOL (width := 8) [0, 1, 2] 0 8 == [192, 3]) &&
  (writeBitmapHOL (width := 8) [2, 0, 1] 0 8 == [192, 3])

#eval writeBitmapParityGuard
#guard writeBitmapParityGuard

example : writeBitmapHOL (width := 8) [0, 1, 2] 0 8 =
    writeBitmapHOL (width := 8) [2, 0, 1] 0 8 :=
  writeBitmapHOL_domain_insensitive [0, 1, 2] [2, 0, 1] 0 8
    (by intro r; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)

/-!
## `insert_bitmap` oracle parity

`Flapjack.Compiler.Backend.WordToStack.insertBitmap` is the exact generic-`α`
port of HOL `insert_bitmap_def` (`word_to_stackScript.sml:246-250`).  The HOL
definition uses no word operation, so the `app_list`/`num` result is compared
structurally here.  Rows from the direct HOL `EVAL` probe
`scripts/hol-probes/word_to_stack_insert_bitmap_probe.out`:

```
ib_empty=((Append Nil (List []),0),0)
ib_flat=((Append (List [9; 8]) (List [1; 2; 3]),8),5)
ib_nested=((Append (Append (List [1]) (List [2])) (List [4]),8),7)
ib_data_len=5   ib_new_len=8
```
-/

def insertBitmapParityGuard : Bool :=
  (match insertBitmap (α := Nat) ([] : List Nat) (AppList.nil, 0) with
   | ((AppList.append AppList.nil (AppList.list []), 0), 0) => true
   | _ => false) &&
  (match insertBitmap (α := Nat) [1, 2, 3] (AppList.list [9, 8], 5) with
   | ((AppList.append (AppList.list [9, 8]) (AppList.list [1, 2, 3]), 8), 5) => true
   | _ => false) &&
  (match insertBitmap (α := Nat) [4]
        (AppList.append (AppList.list [1]) (AppList.list [2]), 7) with
   | ((AppList.append (AppList.append (AppList.list [1]) (AppList.list [2]))
          (AppList.list [4]), 8), 7) => true
   | _ => false) &&
  ((insertBitmap (α := Nat) [1, 2, 3] (AppList.list [9, 8], 5)).2 == 5) &&
  ((insertBitmap (α := Nat) [1, 2, 3] (AppList.list [9, 8], 5)).1.2 == 8)

#eval insertBitmapParityGuard
#guard insertBitmapParityGuard

example : insertBitmap (α := Nat) [1, 2, 3] (AppList.list [9, 8], 5) =
    ((AppList.append (AppList.list [9, 8]) (AppList.list [1, 2, 3]), 8), 5) := rfl

/-!
## stack-slot arithmetic oracle parity

`numStackRet`, `skipFree`, `stackArgCount` and `stackFree` are the exact
generic ports of HOL `num_stack_ret_def`, `skip_free_def`, `stack_arg_count_def`
and `stack_free_def` (`word_to_stackScript.sml:417,423,274,281`).  They are pure
`num`/`sum` arithmetic with no word operation, so the ports carry no side
condition.  Rows from the direct HOL `EVAL` probe
`scripts/hol-probes/word_to_stack_stack_slots_probe.out`:

```
ss_num_stack_ret_pair=2   ss_num_stack_ret_three=1   ss_skip_free_pair=5
ss_arg_count_inl=5        ss_arg_count_inr=4
ss_stack_free_inr=3       ss_stack_free_inl=2
```
-/

def stackSlotsParityGuard : Bool :=
  (numStackRet 1 [10, 20] == 2) &&
  (numStackRet (α := Nat) 3 [10, 20, 30] == 1) &&
  (skipFree (α := Nat) 1 7 9 [10, 20] == 5) &&
  (stackArgCount (α := Nat) (β := Nat) (Sum.inl 4) 7 2 == 5) &&
  (stackArgCount (α := Nat) (β := Nat) (Sum.inr 4) 7 2 == 4) &&
  (stackFree (α := Nat) (β := Nat) (Sum.inr 4) 7 2 7 9 == 3) &&
  (stackFree (α := Nat) (β := Nat) (Sum.inl 4) 7 2 7 9 == 2)

#eval stackSlotsParityGuard
#guard stackSlotsParityGuard

example : numStackRet 1 [10, 20] = 2 := rfl
example : stackArgCount (α := Nat) (β := Nat) (Sum.inr 4) 7 2 = 4 := rfl
example : stackFree (α := Nat) (β := Nat) (Sum.inr 4) 7 2 7 9 = 3 := rfl

/-! ## perf / handler-slot constant oracle parity

Direct HOL `EVAL` rows checked in at
`scripts/hol-probes/word_to_stack_perf_slots_probe.out` (bead
`flapjack-pxn.18.5.15.3.8`):

```
ps_perf_rsp=14   ps_perf_rbp=15
ps_handler_slots_true=5   ps_handler_slots_false=3
```
-/

def perfSlotsParityGuard : Bool :=
  (perfRsp == 14) && (perfRbp == 15) &&
  (handlerSlots true == 5) && (handlerSlots false == 3)

#eval perfSlotsParityGuard
#guard perfSlotsParityGuard

example : perfRsp = 14 := rfl
example : perfRbp = 15 := rfl
example : handlerSlots true = 5 := rfl
example : handlerSlots false = 3 := rfl

/-! ## register-format helper oracle parity

Direct HOL `EVAL` rows checked in at
`scripts/hol-probes/word_to_stack_reg_format_probe.out` (bead
`flapjack-pxn.18.5.15.3.13`):

```
rf_reg1_high=([(3,8)],3)   rf_reg1_low=([],1)
rf_reg2_high=([(4,8)],4)   rf_reg2_low=([],2)
rf_format_var_none=INL 6
rf_format_var_some_reg=INL 2   rf_format_var_some_frame=INR 7
```
-/

open Flapjack.Compiler.Backend.WordToStackRegFormat

def regFormatParityGuard : Bool :=
  (wReg1 8 (3, 10, 12) == ([(3, 8)], 3)) &&
  (wReg1 2 (3, 10, 12) == ([], 1)) &&
  (wReg2 8 (3, 10, 12) == ([(4, 8)], 4)) &&
  (wReg2 4 (3, 10, 12) == ([], 2)) &&
  (formatVar 5 none == Sum.inl 6) &&
  (formatVar 5 (some 2) == Sum.inl 2) &&
  (formatVar 5 (some 7) == Sum.inr 7)

#eval regFormatParityGuard
#guard regFormatParityGuard

example : wReg1 8 (3, 10, 12) = ([(3, 8)], 3) := rfl
example : wReg2 4 (3, 10, 12) = ([], 2) := rfl
example : formatVar 5 none = Sum.inl 6 := rfl
example : formatVar 5 (some 7) = Sum.inr 7 := rfl

/-! ## stack_move / StackArgs oracle parity

Direct HOL `EVAL` rows checked in at
`scripts/hol-probes/word_to_stack_reg_format_probe.out` (bead
`flapjack-pxn.18.5.15.3.14`), for `stack_move` (`word_to_stackScript.sml:288`)
and `StackArgs` (`:293`):

```
sm_zero=T   sm_one=T   sm_two=T   sa_inr=T   sa_inl=T
```

`ProgW` has no `BEq`/`DecidableEq`, so the rows are compared by pattern
matching over the `Seq`/`StackLoad`/`StackStore`/`StackAlloc` fragment.
-/

abbrev StackMoveProg := Flapjack.Compiler.Backend.StackLang.ProgM (BitVec 64)

/-- Structural equality for the `stack_move`/`StackArgs` fragment of `ProgW`. -/
def stackMoveProgBEq : StackMoveProg → StackMoveProg → Bool
  | .skip, .skip => true
  | .seq a b, .seq c d => stackMoveProgBEq a c && stackMoveProgBEq b d
  | .stackLoad r i, .stackLoad s j => r == s && i == j
  | .stackStore r i, .stackStore s j => r == s && i == j
  | .stackAlloc n, .stackAlloc m => n == m
  | _, _ => false

def smSkip : StackMoveProg := .skip
def smSeq (a b : StackMoveProg) : StackMoveProg := .seq a b
def smLoad (r i : Nat) : StackMoveProg := .stackLoad r i
def smStore (r i : Nat) : StackMoveProg := .stackStore r i
def smAlloc (n : Nat) : StackMoveProg := .stackAlloc n

def stackMoveParityGuard : Bool :=
  stackMoveProgBEq (stackMove 0 0 5 3 smSkip) smSkip &&
  stackMoveProgBEq (stackMove 1 0 5 3 smSkip)
    (smSeq smSkip (smSeq (smLoad 3 5) (smStore 3 0))) &&
  stackMoveProgBEq (stackMove 2 0 5 3 smSkip)
    (smSeq (smSeq smSkip (smSeq (smLoad 3 6) (smStore 3 1)))
      (smSeq (smLoad 3 5) (smStore 3 0))) &&
  stackMoveProgBEq (stackArgs (α := Nat) (β := Nat) (γ := BitVec 64)
      (Sum.inr 4) 3 (2, 7, 9)) (smAlloc 0) &&
  stackMoveProgBEq (stackArgs (α := Nat) (β := Nat) (γ := BitVec 64)
      (Sum.inl 4) 7 (2, 7, 9)) (stackMove 5 0 7 2 (smAlloc 5))

#eval stackMoveParityGuard
#guard stackMoveParityGuard

example : stackMove (α := BitVec 64) 0 0 5 3 .skip = .skip := rfl
example : stackArgs (α := Nat) (β := Nat) (γ := BitVec 64)
    (Sum.inr 4) 3 (2, 7, 9) = .stackAlloc 0 := rfl

/-! ## wMoveSingle / wMoveAux oracle parity

Direct HOL `EVAL` rows checked in at
`scripts/hol-probes/word_to_stack_reg_format_probe.out` (bead
`flapjack-pxn.18.5.15.3.15`), for `wMoveSingle` (`word_to_stackScript.sml:62`)
and `wMoveAux` (`:71`):

```
wms_reg_reg=T   wms_reg_frame=T   wms_frame_reg=T   wms_frame_frame=T
wma_empty=T     wma_two=T
```

`ProgW` has no `BEq`/`DecidableEq`, so the rows are compared by pattern
matching; the register-to-register move is the `Inst (Arith (Binop Or ...))`
fragment.
-/

/-- Structural equality for the `wMoveSingle`/`wMoveAux` fragment of `ProgW`,
including the register-to-register `Or` instruction. -/
def wMoveProgBEq : StackMoveProg → StackMoveProg → Bool
  | .skip, .skip => true
  | .seq a b, .seq c d => wMoveProgBEq a c && wMoveProgBEq b d
  | .stackLoad r i, .stackLoad s j => r == s && i == j
  | .stackStore r i, .stackStore s j => r == s && i == j
  | .inst (.arith (.binop .or r1 r2 (.reg r3))),
    .inst (.arith (.binop .or s1 s2 (.reg s3))) =>
    r1 == s1 && r2 == s2 && r3 == s3
  | _, _ => false

def wmsOr (r1 r2 : Nat) : StackMoveProg :=
  .inst (.arith (.binop .or r1 r2 (.reg r2)))

def wMoveParityGuard : Bool :=
  wMoveProgBEq (wMoveSingle (α := BitVec 64) (Sum.inl 3, Sum.inl 5) (2, 7, 9))
    (wmsOr 3 5) &&
  wMoveProgBEq (wMoveSingle (α := BitVec 64) (Sum.inl 3, Sum.inr 5) (2, 7, 9))
    (smLoad 3 3) &&
  wMoveProgBEq (wMoveSingle (α := BitVec 64) (Sum.inr 3, Sum.inl 5) (2, 7, 9))
    (smStore 5 5) &&
  wMoveProgBEq (wMoveSingle (α := BitVec 64) (Sum.inr 3, Sum.inr 5) (2, 7, 9))
    (smSeq (smLoad 2 3) (smStore 2 5)) &&
  wMoveProgBEq (wMoveAux (α := BitVec 64) [] (2, 7, 9)) smSkip &&
  wMoveProgBEq
    (wMoveAux (α := BitVec 64)
      [(Sum.inl 3, Sum.inl 5), (Sum.inr 4, Sum.inr 6)] (2, 7, 9))
    (smSeq (wmsOr 3 5) (smSeq (smLoad 2 2) (smStore 2 4)))

#eval wMoveParityGuard
#guard wMoveParityGuard

example : wMoveSingle (α := BitVec 64) (Sum.inl 3, Sum.inl 5) (2, 7, 9) =
    .inst (.arith (.binop .or 3 5 (.reg 5))) := rfl
example : wMoveAux (α := BitVec 64) [] (2, 7, 9) = .skip := rfl

/-! ## Executable bitmap recursion ↔ tagged recursion

Untagged bridge (bead `flapjack-pxn.18.5.15.3.1.1`): the executed
`Flapjack.RiscV.CakeAlloc` bitmap recursion maps onto the tagged
`bitsToWordW`/`wordListW` for every input, including the out-of-range
`LENGTH > width` boundary (both sides truncate). -/

def bridgeParityGuard : Bool :=
  (BitVec.ofNat 64 (Flapjack.RiscV.CakeAlloc.bitsToWord (List.replicate 65 true)) ==
    bitsToWordW (width := 64) (List.replicate 65 true)) &&
  (BitVec.ofNat 64 (Flapjack.RiscV.CakeAlloc.bitsToWord [true, false, true]) ==
    bitsToWordW (width := 64) [true, false, true]) &&
  ((Flapjack.RiscV.CakeAlloc.frameBitmapWords 4 [true, false]).map (BitVec.ofNat 64) ==
    wordListW (width := 64) [true, false] 4) &&
  ((Flapjack.RiscV.CakeAlloc.frameBitmapWords 2
      [true, true, true, true, true]).map (BitVec.ofNat 64) ==
    wordListW (width := 64) [true, true, true, true, true] 2)

#eval bridgeParityGuard
#guard bridgeParityGuard

/-- Arbitrary-input executable/tagged `bitsToWord` equivalence (stronger than
in-range). -/
example : BitVec.ofNat 64 (Flapjack.RiscV.CakeAlloc.bitsToWord [false, true, true, false]) =
    bitsToWordW (width := 64) [false, true, true, false] :=
  Flapjack.RiscV.CakeAlloc.bitsToWord_ofNat_eq _

/-- The executable chunking maps onto the tagged `wordListW`. -/
example : (Flapjack.RiscV.CakeAlloc.frameBitmapWords 2
      [true, true, true, true, true]).map (BitVec.ofNat 64) =
    wordListW (width := 64) [true, true, true, true, true] 2 :=
  Flapjack.RiscV.CakeAlloc.frameBitmapWords_map 2 _

/-- Kernel-checked equality of the executed bitmap recursion with the tagged
`wordListW`, for the prose-level `dimindex = width` identification. -/
example : (Flapjack.RiscV.CakeAlloc.frameBitmapWords 3 [true, false, true]).map
      (BitVec.ofNat 64) =
    wordListW (width := 64) [true, false, true] 3 :=
  Flapjack.RiscV.CakeAlloc.frameBitmapWords_map 3 _

/-! ## stackLang program-combinator oracle parity

Direct HOL `EVAL` rows checked in at
`scripts/hol-probes/stack_lang_prog_combinators_probe.out` (bead
`flapjack-pxn.18.5.15.3.9`), for the word-independent `prog` combinators
`list_Seq` (`stackLangScript.sml:86`), `SeqStackFree` (`word_to_stackScript.sml:260`),
`wStackLoad` (`:52`) and `wStackStore` (`:57`):

```
lc_empty=Skip                 lc_one=Skip
lc_two=Seq Skip (StackFree 1)
lc_three=Seq Skip (Seq (StackFree 1) Skip)
ssf_zero=Skip                 ssf_two=Seq (StackFree 2) Skip
wsl_empty=Skip
wsl_two=Seq (StackLoad 1 2) (Seq (StackLoad 3 4) Skip)
wss_two=Seq (Seq Skip (StackStore 3 4)) (StackStore 1 2)
```

`Prog` has no `BEq`/`DecidableEq`, so the rows are compared by pattern matching.
-/

open Flapjack.Compiler.Backend.StackLang (listSeq)

abbrev ParityProg := Flapjack.Compiler.Backend.StackLang.Prog Unit Unit Unit Unit Unit Unit Unit

/-- Structural equality for the word-independent `ParityProg` fragment
    (`Prog` has no derived `BEq`/`DecidableEq`). -/
def parityProgBEq : ParityProg → ParityProg → Bool
  | .skip, .skip => true
  | .seq a b, .seq c d => parityProgBEq a c && parityProgBEq b d
  | .stackFree n, .stackFree m => n == m
  | .stackLoad r i, .stackLoad s j => r == s && i == j
  | .stackStore r i, .stackStore s j => r == s && i == j
  | _, _ => false

def vSkip : ParityProg := .skip
def vSeq (a b : ParityProg) : ParityProg := .seq a b
def vStackFree (n : Nat) : ParityProg := .stackFree n
def vStackLoad (r i : Nat) : ParityProg := .stackLoad r i
def vStackStore (r i : Nat) : ParityProg := .stackStore r i

def progCombinatorsParityGuard : Bool :=
  parityProgBEq (listSeq ([] : List ParityProg)) vSkip &&
  parityProgBEq (listSeq ([.skip] : List ParityProg)) vSkip &&
  parityProgBEq (listSeq ([.skip, .stackFree 1] : List ParityProg))
    (vSeq vSkip (vStackFree 1)) &&
  parityProgBEq (listSeq ([.skip, .stackFree 1, .skip] : List ParityProg))
    (vSeq vSkip (vSeq (vStackFree 1) vSkip)) &&
  parityProgBEq (seqStackFree 0 vSkip) vSkip &&
  parityProgBEq (seqStackFree 2 vSkip) (vSeq (vStackFree 2) vSkip) &&
  parityProgBEq (wStackLoad ([] : List (Nat × Nat)) vSkip) vSkip &&
  parityProgBEq (wStackLoad [(1, 2), (3, 4)] vSkip)
    (vSeq (vStackLoad 1 2) (vSeq (vStackLoad 3 4) vSkip)) &&
  parityProgBEq (wStackStore [(1, 2), (3, 4)] vSkip)
    (vSeq (vSeq vSkip (vStackStore 3 4)) (vStackStore 1 2))

#eval progCombinatorsParityGuard
#guard progCombinatorsParityGuard

example : parityProgBEq (listSeq ([] : List ParityProg)) vSkip = true := rfl
example : parityProgBEq (seqStackFree 2 vSkip) (vSeq (vStackFree 2) vSkip) = true := rfl
example : parityProgBEq (wStackLoad [(1, 2), (3, 4)] vSkip)
    (vSeq (vStackLoad 1 2) (vSeq (vStackLoad 3 4) vSkip)) = true := rfl
example : parityProgBEq (wStackStore [(1, 2), (3, 4)] vSkip)
    (vSeq (vSeq vSkip (vStackStore 3 4)) (vStackStore 1 2)) = true := rfl

/-! ## stackLang `store_name` datatype oracle parity

Direct HOL `EVAL` rows checked in at
`scripts/hol-probes/stack_lang_store_name_probe.out` (bead
`flapjack-pxn.18.5.15.3.10`), for the exact monomorphic HOL `store_name`
datatype (`stackLangScript.sml:18-25`):

```
sn_count=18  sn_temp_eq=T  sn_temp_ne=F  sn_find=T  sn_absent=F
sn_temp_w2n=3  sn_temp_word_bits=31
```

`StoreName` has no derived `BEq`/`DecidableEq`, so the checks use structural
pattern matching. -/

open Flapjack.Compiler.Backend.StackLang (StoreName)

/-- Tag every `StoreName` constructor, exercising constructor existence/arity
and the fixed 5-bit `Temp` payload exactly as the HOL datatype declares it. -/
def storeNameTag : StoreName → Nat
  | .nextFree => 0
  | .endOfHeap => 1
  | .triggerGC => 2
  | .heapLength => 3
  | .progStart => 4
  | .bitmapBase => 5
  | .currHeap => 6
  | .otherHeap => 7
  | .allocSize => 8
  | .globals => 9
  | .globReal => 10
  | .handler => 11
  | .genStart => 12
  | .codeBuffer => 13
  | .codeBufferEnd => 14
  | .bitmapBuffer => 15
  | .bitmapBufferEnd => 16
  | .temp value => 17 + value.toNat

def allStoreNames : List StoreName :=
  [.nextFree, .endOfHeap, .triggerGC, .heapLength, .progStart, .bitmapBase,
   .currHeap, .otherHeap, .allocSize, .globals, .globReal, .handler, .genStart,
   .codeBuffer, .codeBufferEnd, .bitmapBuffer, .bitmapBufferEnd,
   .temp (3 : BitVec 5)]

def storeNameParityGuard : Bool :=
  (allStoreNames.length == 18) &&
  (storeNameTag (.temp (3 : BitVec 5)) == 20) &&
  (storeNameTag (.temp (31 : BitVec 5)) == 48) &&
  (storeNameTag .nextFree == 0) &&
  (storeNameTag .bitmapBufferEnd == 16) &&
  (match (StoreName.temp (3 : BitVec 5)) with
   | .temp value => value == 3
   | _ => false)

#eval storeNameParityGuard
#guard storeNameParityGuard

example : storeNameTag (StoreName.temp (3 : BitVec 5)) = 20 := rfl
example : storeNameTag StoreName.allocSize = 8 := rfl
example : storeNameTag (StoreName.temp (31 : BitVec 5)) = 48 := rfl

/-! ## copy_ret_aux / copy_ret oracle parity

Direct HOL `EVAL` rows checked in at
`scripts/hol-probes/word_to_stack_copy_ret_probe.out` (bead
`flapjack-pxn.18.5.15.3.16`), for `copy_ret_aux` (`word_to_stackScript.sml:429`)
and `copy_ret` (`:443`):

```
cra_zero=T  cra_one=T  cra_two=T  cr_zero=T  cr_plain=T  cr_handle=T
```

`ProgM α` has no `BEq`/`DecidableEq`, so the rows are compared by pattern
matching; the fragments use only `Skip`/`Seq`/`StackLoad`/`StackStore` and the
`StackFree` of `SeqStackFree`.
-/

/-- Structural equality for the `copy_ret_aux`/`copy_ret` fragment of `ProgM`. -/
def copyRetProgBEq : StackMoveProg → StackMoveProg → Bool
  | .skip, .skip => true
  | .seq a b, .seq c d => copyRetProgBEq a c && copyRetProgBEq b d
  | .stackLoad r i, .stackLoad s j => r == s && i == j
  | .stackStore r i, .stackStore s j => r == s && i == j
  | .stackFree n, .stackFree m => n == m
  | _, _ => false

def smFree (n : Nat) : StackMoveProg := .stackFree n

def copyRetParityGuard : Bool :=
  copyRetProgBEq (copyRetAux (α := BitVec 64) 3 2 0) smSkip &&
  copyRetProgBEq (copyRetAux (α := BitVec 64) 3 2 1)
    (smSeq (smLoad 3 0) (smSeq (smStore 3 2) smSkip)) &&
  copyRetProgBEq (copyRetAux (α := BitVec 64) 3 2 2)
    (smSeq (smLoad 3 1) (smSeq (smStore 3 3)
      (smSeq (smLoad 3 0) (smSeq (smStore 3 2) smSkip)))) &&
  copyRetProgBEq (copyRet (α := BitVec 64) (β := BitVec 64) false false (2, 7, 9) [] smSkip) smSkip &&
  copyRetProgBEq (copyRet (α := BitVec 64) (β := BitVec 64) false false (2, 7, 9) [10, 20, 30] smSkip)
    (smSeq
      (smSeq (smLoad 2 1) (smSeq (smStore 2 8)
        (smSeq (smLoad 2 0) (smSeq (smStore 2 7) smSkip))))
      (smSeq (smFree 2) smSkip)) &&
  copyRetProgBEq (copyRet (α := BitVec 64) (β := BitVec 64) false true (2, 7, 9) [10, 20, 30] smSkip)
    (smSeq
      (smSeq (smLoad 2 1) (smSeq (smStore 2 11)
        (smSeq (smLoad 2 0) (smSeq (smStore 2 10) smSkip))))
      (smSeq (smFree 2) smSkip))

/-- HOL `copy_ret_def` is polymorphic in the return-value list (`num_stack_ret k
    vs` only measures `LENGTH vs`), so `vs` must be an independent carrier from
    the `ProgM` carrier of `kont`.  The direct HOL oracle rows `cr_plain`/
    `cr_handle` instantiate `vs : num list` against a `64 stackLang$prog`
    continuation; this fixture pins the same independence on the Lean side with
    `β = Nat` and `α = BitVec 64`. -/
def copyRetIndependentGuard : Bool :=
  copyRetProgBEq
    (copyRet (α := BitVec 64) (β := Nat) false false (2, 7, 9) [10, 20, 30] smSkip)
    (smSeq
      (smSeq (smLoad 2 1) (smSeq (smStore 2 8)
        (smSeq (smLoad 2 0) (smSeq (smStore 2 7) smSkip))))
      (smSeq (smFree 2) smSkip))

#eval copyRetParityGuard
#guard copyRetParityGuard
#guard copyRetIndependentGuard

example : copyRetAux (α := BitVec 64) 3 2 0 = .skip := rfl
example : copyRet (α := BitVec 64) (β := BitVec 64) false false (2, 7, 9) [] .skip = .skip := rfl
example : copyRet (α := BitVec 64) (β := Nat) false false (2, 7, 9) [] .skip =
    (copyRet (α := BitVec 64) (β := Nat) false false (2, 7, 9) [] .skip) := rfl

/-- Structural analogue of HOL `wLive_def` (`word_to_stackScript.sml:252`).
    `f = 0` returns `Skip` and the bitmaps unchanged; otherwise it composes
    `write_bitmap`/`insert_bitmap` (oracle rows `wb_empty = [16w]`, `ib_flat`)
    with the exact `Seq`/`Inst`/`Const`/`StackStore` fragment. -/
def wLiveParityGuard : Bool :=
  (match wLiveW (width := 64) [] (Flapjack.AppList.nil, 0) 0 0 4 with
   | (prog, (bitmaps, i)) =>
       (match prog with | .skip => true | _ => false) &&
       (Flapjack.appListAppend bitmaps == []) && (i == 0)) &&
  (match wLiveW (width := 64) [] (Flapjack.AppList.nil, 0) 0 1 4 with
   | (prog, (bitmaps, i)) =>
       (Flapjack.appListAppend bitmaps == [(16 : BitVec 64)]) &&
       (i == 1) &&
       (match prog with
        | .seq (.inst (.const k v)) (.stackStore r off) =>
            (k == 0) && (v == (1 : BitVec 64)) && (r == 0) && (off == 0)
        | _ => false))

#eval wLiveParityGuard
#guard wLiveParityGuard

/-! ## StackHandlerArgs / PushHandler / PopHandler oracle parity

Direct HOL `EVAL` rows checked in at
`scripts/hol-probes/word_to_stack_handler_probe.out` (bead
`flapjack-pxn.18.5.15.3.19`), for `StackHandlerArgs` (`word_to_stackScript.sml:350`),
`PushHandler` (`:355`) and `PopHandler` (`:378`):

```
shaF=T   shaT=T   phF_top=T   phT_top=T   phF_eq=T   pop_eq=T
```

-/

/-- Structural equality for the handler-argument fragment of `ProgM`. -/
def handlerInstBEq : WordLangInst (BitVec 64) → WordLangInst (BitVec 64) → Bool
  | .const r v, .const r' v' => r == r' && v == v'
  | .arith (.binop op d a (.reg n)), .arith (.binop op' d' a' (.reg n')) =>
      op == op' && d == d' && a == a' && n == n'
  | _, _ => false

def handlerProgBEq : StackMoveProg → StackMoveProg → Bool
  | .skip, .skip => true
  | .seq a b, .seq c d => handlerProgBEq a c && handlerProgBEq b d
  | .inst i, .inst j => handlerInstBEq i j
  | .stackAlloc n, .stackAlloc m => n == m
  | .stackFree n, .stackFree m => n == m
  | .stackLoad r i, .stackLoad s j => r == s && i == j
  | .stackStore r i, .stackStore s j => r == s && i == j
  | .stackGetSize r, .stackGetSize s => r == s
  | .locValue r a b, .locValue r' a' b' => r == r' && a == a' && b == b'
  | .get r .handler, .get r' .handler => r == r'
  | .set .handler r, .set .handler r' => r == r'
  | _, _ => false

def hpInstConst (k v : Nat) : StackMoveProg := .inst (.const k (BitVec.ofNat 64 v))
def hpInstOr (k a b : Nat) : StackMoveProg := .inst (.arith (.binop .or k a (.reg b)))
def hpLoc (k l1 l2 : Nat) : StackMoveProg := .locValue k l1 l2
def hpGet (k : Nat) : StackMoveProg := .get k .handler
def hpSet (k : Nat) : StackMoveProg := .set .handler k
def hpSize (k : Nat) : StackMoveProg := .stackGetSize k
def hpFree (k : Nat) : StackMoveProg := .stackFree k

def handlerParityGuard : Bool :=
  (Flapjack.Compiler.Backend.WordToStack.handlerSlots false == 3) &&
  (Flapjack.Compiler.Backend.WordToStack.handlerSlots true == 5) &&
  handlerProgBEq
    (stackHandlerArgs (α := BitVec 64)
      false (Sum.inl 4) 7 (2, 7, 9))
    (stackArgs (α := Nat) (β := Nat) (γ := BitVec 64) (Sum.inl 4) 7 (2, 10, 12)) &&
  handlerProgBEq
    (stackHandlerArgs (α := BitVec 64)
      true (Sum.inr 4) 7 (2, 7, 9))
    (stackArgs (α := Nat) (β := Nat) (γ := BitVec 64) (Sum.inr 4) 7 (2, 12, 14)) &&
  handlerProgBEq
    (popHandler (α := BitVec 64) false (1, 2, 3) smSkip)
    (smSeq (smLoad 1 2) (smSeq ((.set .handler 1) : StackMoveProg)
      (smSeq (hpFree 3) smSkip))) &&
  handlerProgBEq
    (pushHandlerW (width := 64) false 1 2 (3, 4, 5))
    (smSeq (smAlloc 3) (smSeq (hpInstConst 3 1) (smSeq (smStore 3 0)
      (smSeq (hpLoc 3 1 2) (smSeq (smStore 3 1) (smSeq (hpGet 3)
        (smSeq (smStore 3 2) (smSeq smSkip (smSeq (hpSize 3) (hpSet 3)))))))))) &&
  handlerProgBEq
    (pushHandlerW (width := 64) true 1 2 (3, 4, 5))
    (smSeq (smAlloc 5) (smSeq (hpInstConst 3 1) (smSeq (smStore 3 0)
      (smSeq (hpLoc 3 1 2) (smSeq (smStore 3 1) (smSeq (hpGet 3)
        (smSeq (smStore 3 2) (smSeq (smSeq (hpInstOr 3 14 14)
          (smSeq (smStore 3 3) (smSeq (hpInstOr 3 15 15) (smStore 3 4))))
          (smSeq (hpSize 3) (hpSet 3))))))))))

#eval handlerParityGuard
#guard handlerParityGuard

example : stackHandlerArgs (α := BitVec 64)
    false (Sum.inl 4) 7 (2, 7, 9)
    = stackArgs (α := Nat) (β := Nat) (γ := BitVec 64) (Sum.inl 4) 7 (2, 10, 12) := rfl
example : popHandler (α := BitVec 64) false (1, 2, 3) .skip
    = .seq (.stackLoad 1 2) (.seq (.set .handler 1) (.seq (.stackFree 3) .skip)) := rfl

/-!
## `call_dest` and stub-constant oracle parity

`call_dest_def` (`word_to_stackScript.sml:264`) plus `stack_num_stubs_def` /
`word_num_stubs_def` (`backend_commonScript.sml:124/128`) and
`raise_stub_location_def` / `store_consts_stub_location_def`
(`wordLangScript.sml:70/73`), checked in
`scripts/hol-probes/word_to_stack_call_dest_probe.out`.
-/

private def callDestSomeSum : Flapjack.Compiler.Backend.StackLang.ProgM Nat × Sum Nat Nat → Bool
  | (.skip, .inl 3) => true
  | _ => false

private def callDestNoneRegSum : Flapjack.Compiler.Backend.StackLang.ProgM Nat × Sum Nat Nat → Bool
  | (.skip, .inr 1) => true
  | _ => false

private def callDestNoneStackSum : Flapjack.Compiler.Backend.StackLang.ProgM Nat × Sum Nat Nat → Bool
  | (.seq (.stackLoad 3 4) .skip, .inr 3) => true
  | _ => false

private def callDestEmptySum : Flapjack.Compiler.Backend.StackLang.ProgM Nat × Sum Nat Nat → Bool
  | (.skip, .inl 5) => true
  | _ => false

def callDestParityGuard : Bool :=
  (callDestSomeSum (callDest (some 3) [1, 2] (2, 7, 9))) &&
  (callDestNoneRegSum (callDest none [1, 2] (2, 7, 9))) &&
  (callDestNoneStackSum (callDest none [1, 8] (2, 7, 9))) &&
  (callDestEmptySum (callDest none [] (2, 7, 9))) &&
  (Flapjack.stackNumStubs == 5) &&
  (Flapjack.wordNumStubs == 7) &&
  (Flapjack.raiseStubLocation == 5) &&
  (Flapjack.storeConstsStubLocation == 6)

#eval callDestParityGuard
#guard callDestParityGuard

example : callDest (α := Nat) (some 3) [1, 2] (2, 7, 9) = (.skip, .inl 3) := rfl
example : callDest (α := Nat) none [1, 2] (2, 7, 9) = (.skip, .inr 1) := rfl
example : callDest (α := Nat) none [1, 8] (2, 7, 9)
    = (.seq (.stackLoad 3 4) .skip, .inr 3) := rfl
example : callDest (α := Nat) none [] (2, 7, 9) = (.skip, .inl 5) := rfl
example : Flapjack.raiseStubLocation = 5 := rfl

/-!
## `perf_call_prefix`/`perf_call_suffix` and stub oracle parity

`perf_call_prefix_def` (`word_to_stackScript.sml:319`), `perf_call_suffix_def`
(`:336`), `raise_stub_def` (`:557`) and `store_consts_stub_def` (`:578`),
checked in `scripts/hol-probes/word_to_stack_stub_probe.out`.
-/

private def stubAddrsBEq : WordLangAddr (BitVec 64) → WordLangAddr (BitVec 64) → Bool
  | .addr b o, .addr b' o' => b == b' && o == o'

private def stubInstsBEq : WordLangInst (BitVec 64) → WordLangInst (BitVec 64) → Bool
  | .const r v, .const r' v' => r == r' && v == v'
  | .mem op r a, .mem op' r' a' => op == op' && r == r' && stubAddrsBEq a a'
  | .arith (.binop op d s (.imm v)), .arith (.binop op' d' s' (.imm v')) =>
      op == op' && d == d' && s == s' && v == v'
  | .arith (.binop op d s (.reg n)), .arith (.binop op' d' s' (.reg n')) =>
      op == op' && d == d' && s == s' && n == n'
  | _, _ => false

private def stubProgBEq : StackMoveProg → StackMoveProg → Bool
  | .skip, .skip => true
  | .seq a b, .seq c d => stubProgBEq a c && stubProgBEq b d
  | .inst i, .inst j => stubInstsBEq i j
  | .locValue r a b, .locValue r' a' b' => r == r' && a == a' && b == b'
  | .get r .handler, .get r' .handler => r == r'
  | .set .handler r, .set .handler r' => r == r'
  | .stackSetSize r, .stackSetSize s => r == s
  | .stackLoad r i, .stackLoad s j => r == s && i == j
  | .stackStore r i, .stackStore s j => r == s && i == j
  | .stackFree n, .stackFree m => n == m
  | .raise r, .raise r' => r == r'
  | .storeConsts s b o, .storeConsts s' b' o' => s == s' && b == b' && o == o'
  | .ret r, .ret r' => r == r'
  | _, _ => false

private def spSkip : StackMoveProg := .skip
private def spSeq (a b : StackMoveProg) : StackMoveProg := .seq a b
private def spLoc (k l1 l2 : Nat) : StackMoveProg := .locValue k l1 l2
private def spMemStore (r base : Nat) (off : Int) : StackMoveProg :=
  .inst (.mem .store r (.addr base (BitVec.ofInt 64 off)))
private def spMemLoad (r base : Nat) (off : Int) : StackMoveProg :=
  .inst (.mem .load r (.addr base (BitVec.ofInt 64 off)))
private def spArithImm (op : BinOp) (d s : Nat) (v : Int) : StackMoveProg :=
  .inst (.arith (.binop op d s (.imm (BitVec.ofInt 64 v))))
private def spArithReg (op : BinOp) (d s r : Nat) : StackMoveProg :=
  .inst (.arith (.binop op d s (.reg r)))
private def spStackLoad (r i : Nat) : StackMoveProg := .stackLoad r i
private def spStackFree (n : Nat) : StackMoveProg := .stackFree n
private def spStackSetSize (k : Nat) : StackMoveProg := .stackSetSize k
private def spGet (k : Nat) : StackMoveProg := .get k .handler
private def spSet (k : Nat) : StackMoveProg := .set .handler k
private def spRaise (k : Nat) : StackMoveProg := .raise k

private def spRaiseStubTail (k : Nat) (perfPart : StackMoveProg) (slots : Nat) : StackMoveProg :=
  spSeq (spGet k) (spSeq (spStackSetSize k) (spSeq perfPart
    (spSeq (spStackLoad k 2) (spSeq (spSet k) (spSeq (spStackLoad k 1)
      (spSeq (spStackFree slots) (spRaise k)))))))

private def spRaisePerfPart : StackMoveProg :=
  spSeq (spStackLoad 3 3) (spSeq (spArithReg .or 14 3 3)
    (spSeq (spStackLoad 3 4) (spArithReg .or 15 3 3)))

private def spPrefixTree : StackMoveProg :=
  spSeq (spLoc 3 1 2) (spSeq (spMemStore 3 14 (-8)) (spSeq (spMemStore 15 14 (-16))
    (spSeq (spArithImm .sub 14 14 16) (spArithReg .or 15 14 14))))

private def spSuffixTree : StackMoveProg :=
  spSeq (spMemLoad 15 14 0) (spArithImm .add 14 14 16)

def stubParityGuard : Bool :=
  stubProgBEq (perfCallPrefixW (width := 64) 1 2 3) spPrefixTree &&
  stubProgBEq (perfCallSuffixW (width := 64)) spSuffixTree &&
  stubProgBEq (raiseStub (α := BitVec 64) false 3) (spRaiseStubTail 3 spSkip 3) &&
  stubProgBEq (raiseStub (α := BitVec 64) true 3) (spRaiseStubTail 3 spRaisePerfPart 5) &&
  stubProgBEq (storeConstsStub (α := BitVec 64) 3)
    (spSeq (.storeConsts 3 4 none) (.ret 0))

#eval stubParityGuard
#guard stubParityGuard

example : storeConstsStub (α := BitVec 64) 3
    = .seq (.storeConsts 3 4 none) (.ret 0) := rfl
example : raiseStub (α := BitVec 64) false 3
    = spRaiseStubTail 3 spSkip 3 := rfl

def runChecks : IO Bool := do
  IO.println "PASS Word-to-Stack HOL bitmap, stack-slot, and program-combinator oracle rows"
  IO.println "PASS executable Cake bitmap recursion maps to tagged bitsToWordW/wordListW"
  IO.println "PASS stackLang store_name datatype oracle rows"
  pure (parityGuard && wordListParityGuard && chunkToBitsParityGuard &&
    chunkToBitmapParityGuard && writeBitmapParityGuard && insertBitmapParityGuard &&
    stackSlotsParityGuard && perfSlotsParityGuard && bridgeParityGuard &&
    progCombinatorsParityGuard && storeNameParityGuard && regFormatParityGuard &&
    stackMoveParityGuard && wMoveParityGuard && copyRetParityGuard &&
    copyRetIndependentGuard && wLiveParityGuard && handlerParityGuard &&
    callDestParityGuard && stubParityGuard)

end Flapjack.Test.WordToStackBitsParity
