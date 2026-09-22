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

The `callee_abi` fixture now reaches the same Cake ABI registers and exact
return bytes through the production pipeline.  The guards below retain the
source-level calling-convention facts that made that parity repair observable.
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
  wordInstSelectProgramFrom (α := Nat)
    (.assign 5 (.op .add [.var 2, .var 4]))

def selectedBinaryAssignmentShape : Bool :=
  match selectedBinaryAssignment with
  | .seq (.move 0 [(6, 4)])
      (.seq (.move 0 [(7, 2)])
        (.inst (.arith (.binOp .add 5 6 (.reg 7))))) => true
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
      (.inst (.arith (.binOp .add 5 6 (.reg 7))) : WordProg Nat) with
  | some (.inst (.arith (.binOp .add 0 1 (.reg 2)))) => true
  | _ => false

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

/-! Cake keeps a `base + offset` address in expression form while selecting a
    load/store address; Word-to-Stack then folds the offset into the memory
    instruction.  This guard prevents the target-specific immediate selector
    from changing that source-shaped address lowering. -/
def selectedAddressExpressionShape : Bool :=
  match wordInstSelectAddressAtom (α := Word 64) 3
      (.op .add [.var 2, .const (8 : Word 64)]) with
  | (.move 0 [(3, 2)], .op .add [.var 3, .const 8]) => true
  | _ => false

#guard selectedAddressExpressionShape

/-! ## Polymorphic carrier and immediate alignment (bead `flapjack-pxn.9`)

Cake's `asmScript.sml` defines
`reg_imm = Reg reg | Imm ('a imm)` and
`inst = Const reg ('a word) | Arith arith | Mem memop reg ('a addr)`, so the
carrier keeps the immediate operand rather than specializing it to a host
`Nat`.  These guards pin that an immediate-carrying arithmetic instruction and
a constant instruction lower to the architectural immediate forms, and that
the stack lowering preserves the immediate operand and configured locations. -/

def immediateCarrierInstruction : Bool :=
  match wordInstToInstruction (width := 64)
      (.arith (.binOp .add 1 2 (.imm 5)) : WordInst (Word 64)) with
  | some (.addi destination source immediate) =>
      destination = 1 ∧ source = 2 ∧ immediate = 5
  | _ => false

#guard immediateCarrierInstruction

/- Cake's `riscv_ast` handles `Binop Sub ... (Imm i)` separately from
   `riscv_bop_i`: `riscv_targetScript.sml:121` emits ADDI with the
   two's-complement immediate `-i`.  Keep this direct carrier boundary
   explicit so a future immediate specialization cannot silently select a
   non-Cake subtraction form. -/
def subImmediateCarrierInstruction : Bool :=
  match wordInstToInstruction (width := 64)
      (.arith (.binOp .sub 1 2 (.imm (BitVec.ofNat 64 5))) :
        WordInst (Word 64)) with
  | some (.addi destination source immediate) =>
      destination = 1 ∧ source = 2 ∧
        immediate = (0 - BitVec.ofNat 64 5)
  | _ => false

#guard subImmediateCarrierInstruction

/- Cake's `wInst (Arith (Binop ... (Imm ...)))` uses `wReg1` for a spilled
   left operand and `wRegWrite1` for a spilled destination
   (`word_to_stackScript.sml:91-99`).  This direct carrier guard pins the
   source-shaped StackLang sequence, including both frame offsets. -/
def spilledImmediateCarrierShape : Bool :=
  match wordStackArithInst
      { locations := [(1, .stack 2), (2, .stack 3)]
        scratch := 31
        stackBase := 10 }
      (.binOp .add 1 2 (.imm 5) : WordArith Nat) with
  | some (.seq (.stackLoad 31 13)
      (.seq (.inst (.arith (.binOp .add 31 31 (.imm 5))))
        (.stackStore 31 12))) => true
  | _ => false

#guard spilledImmediateCarrierShape

/- Cake's `riscv_bop_i` table keeps an immediate `Or` as one ORI at the
   signed-12 upper boundary (`riscv_targetScript.sml:114-120`).  This direct
   Word backend guard is separate from the spilled-carrier shape above and
   pins the target operation selected for the source-shaped immediate. -/
def immediateOrUpperBoundary : Bool :=
  wordArithToInstruction (width := 64)
      (.binOp .or 4 5 (.imm (BitVec.ofNat 64 2047))) ==
    some (.ori 4 5 (BitVec.ofNat 64 2047))

#guard immediateOrUpperBoundary

def rotateImmediateCarrierInstructions : Bool :=
  match wordArithToInstructions (width := 64)
      (.shift .ror 1 2 (.imm 5) : WordArith (Word 64)) with
  | some [.srli temporary source amount,
      .slli destination source' complement,
      .or destination' destination'' temporary'] =>
      temporary = 31 ∧ source = 2 ∧ amount = 5 ∧
        destination = 1 ∧ source' = 2 ∧ complement = 59 ∧
        destination' = 1 ∧ destination'' = 1 ∧ temporary' = 31
  | _ => false

#guard rotateImmediateCarrierInstructions

def constantCarrierInstruction : Bool :=
  match wordInstToInstruction (width := 64)
      (.const 3 7 : WordInst (Word 64)) with
  | some (.addi destination source immediate) =>
      destination = 3 ∧ source = 0 ∧ immediate = 7
  | _ => false

#guard constantCarrierInstruction

def immediateCarrierLoweringShape : Bool :=
  match
    wordToStackProgWordWithLocationBitmapsFused immediateSelectionConfig 22 0 1 64 none
      (wordStackInitialBitmaps false)
      (.inst (.arith (.binOp .add 6 4 (.imm 1)) : WordInst (Word 64))) with
  | some (.inst (.arith (.binOp .add destination source (.imm value))), _) =>
      destination = 0 ∧ source = 1 ∧ value = 1
  | _ => false

#guard immediateCarrierLoweringShape

/-! Cake's nested `inst_select_exp` path keeps a valid logical immediate in
    `WordInst.Arith`, rather than materialising a constant register before the
    operation (`word_instScript.sml:269-275`). -/
def nestedImmediateCarrierShape : Bool :=
  match wordStackCompileExpToRegisterNat immediateSelectionConfig 6 [11, 10]
      (.op .and [.var 4, .const 1]) with
  | some (.inst (.arith (.binOp .and 6 1 (.imm 1)))) => true
  | _ => false

#guard nestedImmediateCarrierShape

def nestedImmediateShiftCarrierShape : Bool :=
  match wordStackCompileExpToRegisterNat immediateSelectionConfig 6 [11, 10]
      (.shift .lsl (.var 4) (.const 3)) with
  | some (.inst (.arith (.shift .lsl 6 1 (.imm 3)))) => true
  | _ => false

#guard nestedImmediateShiftCarrierShape

def immediateCarrierMachineShape : Bool :=
  let state : WordStackMachineState 64 :=
    { registers := fun register =>
        if register = 4 then BitVec.ofNat 64 7 else 0
      stack := fun _ => 0
      stores := fun _ => 0
      memory := fun _ => 0
      sharedMemory := fun _ => 0 }
  match evalWordStackMachine state
      (.inst (.arith (.binOp .and 6 4 (.imm 1))) : StackProg Nat) with
  | some result => result.registers 6 == BitVec.ofNat 64 1
  | _ => false

#guard immediateCarrierMachineShape

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
  | some (.seq (.inst (.arith (.binOp .add destination left (.imm value)))) .skip, _) =>
      destination = 0 ∧ left = 1 ∧ value = 1
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

/-! Cake's `const_fp_loop` applies `const_fp_exp` to the address of every
    shared-memory operation (`word_simpScript.sml:304-339`), while preserving
    the store's constant environment and deleting a load's destination.  This
    guard is the source-shaped regression for the remaining branch/allocator
    parity fixtures. -/
def sharedAddressConstFpProgram : WordProg (Word 64) :=
  .seq (.assign 4 (.const 0))
    (.seq (.shareInst .load 6 (.var 4))
      (.shareInst .store 2 (.var 4)))

def sharedAddressConstFpMatchesCake : Bool :=
  match RiscV.wordConstFp sharedAddressConstFpProgram with
  | .seq (.seq (.assign 4 (.const 0))
      (.shareInst .load 6 (.const 0)))
      (.shareInst .store 2 (.const 0)) => true
  | _ => false

#guard sharedAddressConstFpMatchesCake

/-! `const_fp_exp` treats an expression-level `Load` as opaque
    (`word_simpScript.sml:191-212`): unlike `ShareInst Load`, it does not
    propagate the constant environment into the load address.  This matters
    for the initialisation order that the allocator sees. -/
def loadAddressConstFpProgram : WordProg (Word 64) :=
  .seq (.assign 4 (.const 0)) (.assign 6 (.load (.var 4)))

def loadAddressConstFpIsOpaque : Bool :=
  match RiscV.wordConstFp loadAddressConstFpProgram with
  | .seq (.assign 4 (.const 0)) (.assign 6 (.load (.var 4))) => true
  | _ => false

#guard loadAddressConstFpIsOpaque

/-! ### Cake copy propagation representative

    Cake's `set_eq` (`compiler/backend/word_copyScript.sml:204-225`) inserts the
    move DESTINATION as the representative of the equivalence class, so
    `copy_prop_inst (Mem Store r (Addr a w))` rewrites the address to the
    destination.  Propagating in the other direction rewrote the destination
    back to the source, which made the move dead and flipped the allocator's
    colouring (`set_globals`). -/
def copyPropagationWordProgram : WordProg (Word 64) :=
  .seq (.move 0 [(37, 25)]) (.inst (.mem .store 33 37))

def copyPropagationKeepsDestination : Bool :=
  match RiscV.wordCopyProp copyPropagationWordProgram with
  | .seq _ (.inst (.mem .store 33 address)) => address == 37
  | _ => false

/-! `Set name (Var n)` records what the store holds and `Get m name` uses it
    (Cake `word_copyScript.sml:233-346`). -/

def copyPropagationSharesStoredValues : Bool :=
  match RiscV.wordCopyProp
      (.seq (.set .currHeap (.var 5)) (.get 9 .currHeap) : WordProg (Word 64)) with
  | .seq (.set .currHeap (.var 5)) (.move 0 [(9, 5)]) => true
  | _ => false

def copyPropagationDropsRedundantGet : Bool :=
  match RiscV.wordCopyProp
      (.seq (.set .currHeap (.var 5)) (.get 5 .currHeap) : WordProg (Word 64)) with
  | .seq (.set .currHeap (.var 5)) .skip => true
  | _ => false

#guard copyPropagationSharesStoredValues
#guard copyPropagationDropsRedundantGet

/-! Cake's `inst_select_exp (Lookup s) = Get tar s`, and `stackLang` store names
    include `Temp`, so the concrete Word-to-Stack path must lower a `Get` from a
    temporary store instead of rejecting it. -/

def selectedLookupGet : Bool :=
  match RiscV.wordInstSelectProgramFrom
      (.assign 6 (.lookup .heapLength) : WordProg (Word 64)) with
  | .get 6 .heapLength => true
  | _ => false

#guard selectedLookupGet

def tempStoreGetConfig : WordStackConfig :=
  { locations := [(5, .register 1)]
    scratch := 22
    stackBase := 0
    addressScratch := 12
    specialScratch := 11
    carryScratch := 10
    abiBase := 1 }

def tempStoreGetLowers : Bool :=
  match RiscV.wordStackGetNat tempStoreGetConfig 5 (.temp 3) with
  | some (.get 1 (.temp 3)) => true
  | _ => false

#guard tempStoreGetLowers

#guard copyPropagationKeepsDestination

/- A later copy through an already-populated class makes its destination the
   representative visible to subsequent moves. -/
def copyPropagationUsesLatestRepresentative : Bool :=
  match RiscV.wordCopyProp
      (.seq (.move 0 [(61, 45), (65, 45)])
        (.move 0 [(297, 65)]) : WordProg (Word 64)) with
  | .seq _ (.move 0 [(297, 61)]) => true
  | _ => false

#guard copyPropagationUsesLatestRepresentative

/- Cake invalidates copy state after a shared-memory store, including copies
   established before the branch containing that store. -/
def copyPropagationInvalidatesShareStore : Bool :=
  match RiscV.wordCopyProp
      (.seq (.move 0 [(301, 297)])
        (.seq (.ite .notLess 301 (.reg 309)
          (.move 0 [(353, 321)])
          (.seq (.move 0 [(341, 337)])
            (.seq (.shareInst .store 341 (.var 345))
              (.move 0 [(353, 349)]))))
          (.move 0 [(381, 297)])) : WordProg (Word 64)) with
  | .seq _ (.seq (.ite _ _ _ _ _) (.move 0 [(381, 297)])) => true
  | _ => false

#guard copyPropagationInvalidatesShareStore

/- A representative update must rewrite all later members of the same Cake
   class, not only the most recently inserted alias.  This is the reduced
   shape of the fp_pow4 table setup: Cake changes the later 413 source from
   the intermediate 329 to the surviving 345 representative. -/
def copyPropagationCollapsesRepresentativeChain : Bool :=
  match RiscV.wordCopyProp
      (.seq (.move 0 [(349, 325), (345, 305), (341, 317), (337, 313),
          (333, 309), (329, 305)])
        (.move 0 [(413, 329)]) : WordProg (Word 64)) with
  | .seq (.move 0 [(349, 325), (345, 305), (341, 317), (337, 313),
      (333, 309), (329, 305)]) (.move 0 [(413, 345)]) => true
  | _ => false

#guard copyPropagationCollapsesRepresentativeChain

/- Cake's `copy_prop_prog (Loop ...)` resets the incoming copy state after
   transforming the loop body (`word_copyScript.sml:377-380`). -/
def copyPropagationClearsLoopState : Bool :=
  match RiscV.wordCopyProp
      (.seq (.move 0 [(61, 45), (65, 45)])
        (.seq (.loop [] (.skip : WordProg (Word 64)) [])
          (.move 0 [(297, 65)])) : WordProg (Word 64)) with
  | .seq _ (.seq (.loop _ _ _) (.move 0 [(297, 65)])) => true
  | _ => false

#guard copyPropagationClearsLoopState

/- Cake's `remove_eq` checks class membership (`to_eq`), not the optional
   representative/alias cache.  Keeping this distinction is necessary for
   the cache-enabled production state: a class member can have no standalone
   alias entry after a representative update. -/
def copyRemoveUsesClassMembership : Bool :=
  let state : RiscV.WordCopyState :=
    { aliases := []
      storeToEq := []
      classOf := [(177, 0)]
      classRep := [(0, 177)]
      classStore := []
      classNext := 1 }
  (RiscV.wordCopyRemove state 177).classNext == 0

#guard copyRemoveUsesClassMembership

/- Cake's `remove_eq` checks class membership (`to_eq`), not the flattened
   representative aliases.  Keeping this distinction prevents a stale alias
   cache from retaining a class that Cake has invalidated. -/
def copyPropagationRemovesByClassMembership : Bool :=
  let classOf : NatInfoMap Nat := [(145, 0)]
  let classRep : NatInfoMap Nat := [(0, 145)]
  let state : RiscV.WordCopyState :=
    { RiscV.wordCopyEmpty with
      aliases := []
      classOf := classOf
      classRep := classRep
      indicesReady := false }
  let removed := RiscV.wordCopyRemove state 145
  removed.classOf == [] && removed.classRep == []

#guard copyPropagationRemovesByClassMembership

/- Cake's branch merge compares class identities, not only the visible
   representative.  Independently-created classes for the same names must
   therefore not propagate a branch-local source across the merge. -/
def copyMergeKeepsClassIdentity : Bool :=
  let left : RiscV.WordCopyState :=
    { aliases := [(2373, 2321), (2321, 2321)]
      storeToEq := []
      classOf := [(2373, 4), (2321, 4)]
      classRep := [(4, 2321)]
      classStore := []
      classNext := 5 }
  let right : RiscV.WordCopyState :=
    { aliases := [(2373, 2321), (2321, 2321)]
      storeToEq := []
      classOf := [(2373, 5), (2321, 5)]
      classRep := [(5, 2321)]
      classStore := []
      classNext := 6 }
  RiscV.wordCopyLookup (RiscV.wordCopyMerge left right) 2373 == 2373

#guard copyMergeKeepsClassIdentity


/- Cake's `merge_eqs` intersects `store_to_eq` by both store name and
   equivalence class.  Two branches that record the same store class must
   therefore retain the following `Get` lookup after the merge. -/
def copyMergeKeepsStoreEquivalence : Bool :=
  let left := RiscV.wordCopySetStoreEq RiscV.wordCopyEmpty 77 145
  let right := RiscV.wordCopySetStoreEq RiscV.wordCopyEmpty 77 145
  let merged := RiscV.wordCopyMerge left right
  RiscV.wordCopyLookupStoreEq merged 77 == some 145


/- Cake's `merge_eqs` is conservative: a store absent from either branch
   cannot survive the intersection, so the merged state must not propagate a
   stale value through a later `Get`. -/
def copyMergeDropsNonCommonStore : Bool :=
  let left := RiscV.wordCopySetStoreEq RiscV.wordCopyEmpty 77 145
  let right := RiscV.wordCopySetStoreEq RiscV.wordCopyEmpty 78 145
  let merged := RiscV.wordCopyMerge left right
  RiscV.wordCopyLookupStoreEq merged 77 == none &&
    RiscV.wordCopyLookupStoreEq merged 78 == none

#guard copyMergeDropsNonCommonStore
#guard copyMergeKeepsStoreEquivalence

/- Cake's `set_store_eq` records both the store-to-class relation and its
   representative.  The production copy state keeps the Cake lists for
   branch intersection, while the lookup-only indexes must expose the same
   value to a following `Get`. -/
def copyStoreEquivalenceIndexGuard : Bool :=
  let state := RiscV.wordCopySetStoreEq RiscV.wordCopyEmpty 77 145
  RiscV.wordCopyLookupStoreEq state 77 == some 145

#guard copyStoreEquivalenceIndexGuard

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
    ("Cake Sub immediate uses signed ADDI", subImmediateCarrierInstruction),
    ("parallel moves preserve a source that a later move reads",
      parallelMoveKeepsLiveSource),
    ("parallel location moves preserve a source that a later move reads",
      parallelLocationMoveKeepsLiveSource),
    ("overflowing Cake ABI arguments reserve frame slots", overflowDemandMatches),
    ("an overflowing call lowers once the frame demand is reserved",
      overflowLowersWithDemandFrame),
    ("an overflowing call is rejected without that frame room",
      overflowRejectedWithTinyFrame),
    ("copy propagation keeps Cake's destination representative",
      copyPropagationKeepsDestination),
    ("copy propagation removes by Cake class membership",
      copyPropagationRemovesByClassMembership),
    ("copy propagation shares a stored value", copyPropagationSharesStoredValues),
    ("copy propagation drops a redundant Get", copyPropagationDropsRedundantGet)]
  let mut ok := true
  for (label, passed) in checks do
    if passed then
      IO.println s!"PASS {label}"
    else
      IO.println s!"FAIL {label}"
      ok := false
  return ok

end Flapjack.Test.RiscVAbiParity
