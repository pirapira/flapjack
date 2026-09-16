import Flapjack.RiscV.PipelineDiagnostics

/-!
# CakeML RISC-V calling-convention parity

Regression coverage for the multi-function argument/return ABI (GitHub issue
#1024, bead `flapjack-pxn.8.5.10.1.1`).

Oracle evidence: the original compiler emits

```
fun 1 g(1 a, 1 b) { return a + b; }        -> add a0, a1, a0; ret
fun 1 h(1 a,1 b,1 c,1 d) { ... }           -> add a1,a1,a0; add a0,a3,a2; ...
```

so value argument `j` arrives in hardware register `riscv_names (j+1)`
(`a0..a3` = `10,11,12,13`) and the incoming link register is hardware `1`
(`riscv_names 0`).  The original allocator's `arg_count` therefore counts the
link slot as well, and its ABI word names are `[0, 2, 4, ..., 2n]` for `n`
value parameters.  Both facts are pinned here against the ported
`riscvRegisterName` map (`scripts/hol-probes/riscv_names_probe.out`).

The blocking piece for byte parity is that Flapjack's lowered function body
keeps the link entry move (and does not coalesce parameters onto the ABI
registers), while the original runs `remove_dead_prog` right after
`full_ssa_cc_trans` (`compiler/backend/backend_passesScript.sml:206-207`); see
the `callee_abi` fixture and bead `flapjack-pxn.8.5.10.1.1`.
-/

namespace Flapjack.Test.RiscVAbiParity

open Flapjack Flapjack.RiscV

/-- Hardware argument registers of the original compiler for `j = 0..3`,
read from the emitted bodies of `fun 1 g(1 a, 1 b)` and
`fun 1 h(1 a, 1 b, 1 c, 1 d)`. -/
def cakeAbiArgumentRegisters : List Nat := [10, 11, 12, 13]

/-- The ported `riscv_names` map puts value argument `j` in the same hardware
register the original compiler uses. -/
def abiArgumentRegistersMatch : Bool :=
  (List.range 4).all (fun j => riscvRegisterName (j + 1) == cakeAbiArgumentRegisters[j]!)

/-- The incoming link register is hardware `1` (`riscv_names 0`). -/
def abiLinkRegisterMatches : Bool :=
  riscvRegisterName 0 == 1

/-- Cake's `arg_count` counts the incoming link slot, so a function with two
value parameters presents three ABI word names: the link and both arguments.
The port exposes this as `wordSsaAbiParameters (parameters.length + 1)`; the
source-to-RISC-V pipeline still passes only `parameters.length`, which is the
tracked gap behind the `callee_abi` fixture. -/
def abiNamesIncludeLinkSlot : Bool :=
  wordSsaAbiParameters (2 + 1) == [0, 2, 4]

/-- Configuration whose locations map names onto themselves, so a move of
`(destination, source)` emits exactly one register copy. -/
def parallelMoveConfig : WordStackConfig :=
  { locations := [(1, .register 1), (2, .register 2), (3, .register 3)]
    scratch := 31
    stackBase := 0
    addressScratch := 29
    specialScratch := 28
    carryScratch := 27
    abiBase := 10 }

/-- A parallel move whose second destination still reads the first
destination must copy the original source value first.  For
`{r1 <- r2, r3 <- r1}` the only correct sequence preserves the old `r1` in
`r3`, i.e. `r3 <- r1` runs last.  Emitting the ready move first (the previous
behaviour) produced `r1 <- r2; r3 <- r1`, giving `r3 = r2`, which broke the
callee entry moves measured in GitHub issue #1024. -/
def parallelMoveKeepsLiveSource : Bool :=
  match wordStackParallelMove (α := Nat) parallelMoveConfig [(1, 2), (3, 1)] with
  | some (.seq (.arith .or 3 1 1) (.arith .or 1 2 2)) => true
  | _ => false

/-! The same dependency order for the `WordLocation` scheduler, which drives
    the call argument/return and FFI moves.  For `{r3 <- r1, r1 <- r2}` the
    ready move `r1 <- r2` is emitted first and the postponed `r3 <- r1` last, so
    `r3` keeps the original `r1` instead of the new `r2`. -/
def parallelLocationMoveKeepsLiveSource : Bool :=
  match wordStackParallelLocationMove (α := Nat) parallelMoveConfig
      [(.register 3, .register 1), (.register 1, .register 2)] with
  | some (.seq (.arith .or 3 1 1) (.arith .or 1 2 2)) => true
  | _ => false

#guard abiArgumentRegistersMatch
#guard abiLinkRegisterMatches
#guard abiNamesIncludeLinkSlot
#guard parallelMoveKeepsLiveSource
#guard parallelLocationMoveKeepsLiveSource

/-! Cake's `inst_select_exp` materializes the two operands in successive
    temporaries and then emits an arithmetic instruction whose operands are
    those temporaries as register numbers
    (`word_instScript.sml:269-279`:
    `Seq p1 (Seq p2 (Inst (Arith (Binop op tar temp (Reg (temp+1))))))`).
    Keeping the operands as registers rather than as rewritable expressions is
    what stops `copy_prop` from folding the operand copies away, which is
    observable in the register allocator's coalescing decisions (the
    `callee_abi` fixture used to emit `add a1,a1,a0; or a0,a1,a1` instead of
    the original `add a0,a1,a0`). -/
def selectedBinaryAssignment : WordProg Nat :=
  wordInstSelectProgramFrom
    (.assign 5 (.op .add [.var 2, .var 4]))

def selectedBinaryAssignmentShape : Bool :=
  match selectedBinaryAssignment with
  | .seq (.assign 6 (.var 4))
      (.seq (.assign 7 (.var 2))
        (.inst (.arith (.binOp .add 5 6 7)))) => true
  | _ => false

#guard selectedBinaryAssignmentShape

/-! The register-operand carrier lowers exactly like the expression assignment
    it replaces, so the emitted stack program does not change. -/
def selectedBinaryGroundConfig : WordStackConfig :=
  { locations := [(5, .register 0), (6, .register 1), (7, .register 2)]
    scratch := 22
    stackBase := 0
    addressScratch := 12
    specialScratch := 11
    carryScratch := 10
    abiBase := 1 }

def selectedBinaryCarrierLowering : Bool :=
  match
    wordToStackProgNat selectedBinaryGroundConfig
      (.inst (.arith (.binOp .add 5 6 7))),
    wordToStackProgNat selectedBinaryGroundConfig
      (.assign 5 (.op .add [.var 6, .var 7])) with
  | some (.arith .add 0 1 2), some (.arith .add 0 1 2) => true
  | _, _ => false

#guard selectedBinaryCarrierLowering

def twoRegisterAssignmentShape : Bool :=
  match wordThreeToTwoReg
      (.assign 5 (.op .add [.var 6, .var 7]) : WordProg Nat) with
  | .seq (.move 0 [(5, 6)])
      (.assign 5 (.op .add [.var 5, .var 7])) => true
  | _ => false

#guard twoRegisterAssignmentShape

/-! Immediate-selected arithmetic is carried to Lab as the existing
    const-plus-arithmetic fusion shape, including the non-in-place result
    case used by Cake's `Binop ... (Imm ...)`. -/
def immediateSelectionConfig : WordStackConfig :=
  { locations := [(4, .register 1), (6, .register 0)]
    scratch := 22
    stackBase := 0
    addressScratch := 12
    specialScratch := 11
    carryScratch := 10
    abiBase := 1 }

def immediateSelectionShape : Bool :=
  match wordStackCompileExpNat immediateSelectionConfig 6
      (.op .add [.var 4, .const 1]) with
  | some (.seq (.arith .or 12 1 1)
      (.seq (.const 22 1) (.arith .add 0 12 22))) => true
  | _ => false

#guard immediateSelectionShape

/-! The two-register compensation introduces `Move 0 [(destination, left)]`
    before an in-place immediate operation.  Cake instead keeps the operand in
    the temporary chosen by `inst_select` and reads it while writing the
    destination (`Binop op tar temp (Imm w)`), so the lowering must re-read the
    move's source instead of copying it into the destination first.  This is
    what removed the leftover `or a0,ra,ra` in the `callee_abi` fixture. -/
def immediateCompensationWordProgram : WordProg (Word 64) :=
  .seq (.move 0 [(6, 4)])
    (.seq (.assign 6 (.op .add [.var 6, .const 1])) .skip)

def immediateCompensationShape : Bool :=
  match wordToStackProgWordWithLocationBitmapsFused immediateSelectionConfig
      22 0 1 64 none (wordStackInitialBitmaps false)
      immediateCompensationWordProgram with
  | some (.seq (.seq (.const constant value) (.arith .add destination left right)) _, _) =>
      constant != destination && left != destination && right == constant && value == 1
  | _ => false

#guard immediateCompensationShape

/-! ### Cake constant propagation before calls

    Cake's `word_simp$const_fp` re-materialises the arguments of a call with
    `SmartSeq (drop_consts cs args) (Call ...)` and `drop_consts` recurses on
    the TAIL before emitting the head assignment, so the emitted constant
    writes appear in reverse argument order
    (`compiler/backend/word_simpScript.sml:270-308`).  SSA and `remove_dead`
    later delete the superseded earlier copies, which is why Cake's RISC-V
    output carries the second argument's constant first.  This is the
    `callee_abi` ordering defect. -/
def dropConstsWordProgram : WordProg (Word 64) :=
  .seq (.assign 6 (.const 5))
    (.seq (.assign 2 (.const 7)) (.call none (some 5) [6, 2] none))

def dropConstsReversesArguments : Bool :=
  match (RiscV.wordProgSeqItems (RiscV.wordConstFp dropConstsWordProgram)).reverse with
  | .call _ _ [6, 2] _ :: .assign 6 (.const 5) :: .assign 2 (.const 7) :: _ => true
  | _ => false

#guard dropConstsReversesArguments

/-! ### Cake ABI argument overflow

    The original `format_var`/`wMoveSingle` materializes arguments past the
    register window at the top of the frame, and sizes the frame with
    `stack_var_count = MAX ((max_var DIV 2 + 1) - k) stack_arg_count`
    (`word_to_stackScript.sml:586-592`), so the frame always has room for the
    stack-passed arguments.  Without that room Flapjack's physical argument
    destinations collide and the parallel move refuses to lower: the guest
    `generic_create` calls a 17-argument function and reported
    `wordToStackFailure 544 []` with `abiRegisterCount = 12`, i.e. five
    stack-passed arguments needing `17 - 12 - 1 = 4` frame slots. -/

def overflowArguments : List Nat :=
  [2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34]

def overflowingCallProgram : WordProg Nat :=
  .call none (some 7) overflowArguments none

def overflowConfig : WordStackConfig :=
  { locations := overflowArguments.zip
      ((List.range overflowArguments.length).map
        (fun index => WordLocation.register (index + 2)))
    scratch := 31
    stackBase := 0
    addressScratch := 29
    specialScratch := 28
    carryScratch := 27
    abiBase := 10
    abiStride := 1
    abiFrameSlots := 0 }

def overflowDemandMatches : Bool :=
  wordProgMaxCallArguments overflowingCallProgram == 17 &&
    wordProgMaxCallArguments (.call none (some 7) [2, 4, 6] none : WordProg Nat) == 3

def overflowLowersWithDemandFrame : Bool :=
  let demand := wordProgMaxCallArguments overflowingCallProgram - 12
  match wordToStackProgNatWithLocationBitmaps
      { overflowConfig with abiFrameSlots := demand }
      25 31 demand 64 (some 1) (wordStackInitialBitmaps false)
      overflowingCallProgram with
  | some _ => true
  | none => false

def overflowRejectedWithTinyFrame : Bool :=
  match wordToStackProgNatWithLocationBitmaps
      { overflowConfig with abiFrameSlots := 1 }
      25 31 1 64 (some 1) (wordStackInitialBitmaps false)
      overflowingCallProgram with
  | some _ => false
  | none => true

#guard overflowDemandMatches
#guard overflowLowersWithDemandFrame
#guard overflowRejectedWithTinyFrame

def runChecks : IO Bool := do
  let checks := [
    ("the Cake ABI argument registers match riscv_names", abiArgumentRegistersMatch),
    ("the Cake ABI link register is hardware one", abiLinkRegisterMatches),
    ("the Cake ABI name list includes the link slot", abiNamesIncludeLinkSlot),
    ("parallel moves preserve a source that a later move reads",
      parallelMoveKeepsLiveSource),
    ("parallel location moves preserve a source that a later move reads",
      parallelLocationMoveKeepsLiveSource),
    ("overflowing Cake ABI arguments reserve frame slots", overflowDemandMatches),
    ("an overflowing call lowers once the frame demand is reserved",
      overflowLowersWithDemandFrame),
    ("an overflowing call is rejected without that frame room",
      overflowRejectedWithTinyFrame)]
  let mut ok := true
  for (label, passed) in checks do
    if passed then
      IO.println s!"PASS {label}"
    else
      IO.println s!"FAIL {label}"
      ok := false
  return ok

end Flapjack.Test.RiscVAbiParity
