import Flapjack.Lab

namespace Flapjack

def labStackRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

example :
    labFlatten false 20 7 [] []
      (.ffi "sum" 1 2 3 4 9 : StackProg Nat) =
      { lines := [
          .labAsm (.locValue 9 ⟨20, 7⟩) [] 0,
          .labAsm (.callFfi "sum") [] 0,
          .label 20 7 0],
        terminal := false,
        nextLabel := 8 } := by
  simp [labFlatten, labLabel]

example :
    labFlatten false 3 4 [] []
      (.loop (.seq (.tick) (.break 0)) : StackProg Nat) =
      { lines := [
          .label 3 4 0,
          .asm .tick [] 0,
          .labAsm (.jump ⟨3, 5⟩) [] 0,
          .labAsm (.jump ⟨3, 4⟩) [] 0,
          .label 3 5 0],
        terminal := false,
        nextLabel := 6 } := by
  simp [labFlatten, labLabel, labJump, labFindLabel]

example :
    labProgramToSection 2 3
      (.seq (.tick) (.return 4) : StackProg Nat) =
      ⟨2, [
        .asm .tick [] 0,
        .label 2 1 0,
        .labAsm .return [] 0,
        .label 2 3 0]⟩ := by
  simp [labProgramToSection, labFlatten, labIsSequence, labLabel]

example :
    labFlatten false 2 3 [] []
      (.seq (.arith .add 4 5 6) (.shift .lsl 7 8 9) : StackProg Nat) =
      { lines := [
          .asm (.arith .add 4 5 6) [] 0,
          .asm (.shift .lsl 7 8 9) [] 0],
        terminal := false,
        nextLabel := 3 } := by
  simp [labFlatten]

/- CakeML's final Lab filter removes a physical identity move.  This is the
   concrete artifact-side counterpart of the Word-to-Stack parallel-move
   identity case and must not leave a one-instruction hole in the section. -/
example :
    labFlatten false 2 3 [] []
      (.arith .or 7 7 7 : StackProg Nat) =
      { lines := [], terminal := false, nextLabel := 3 } := by
  simp [labFlatten]

example :
    labProgramToSectionAfterStackRemove labStackRemoveConfig 2 3
      (.get 4 .heapLength : StackProg Nat) =
      ⟨2, [
        .asm (.memOffset .load .sub 4 10 24) [] 0,
        .label 2 3 0]⟩ := by
  simp [labProgramToSectionAfterStackRemove, labProgramToSection,
    stackRemoveComplete, stackRemoveFuel, stackProgDepth, stackRemoveGet,
    stackRemoveAddress,
    stackRemoveJoin, stackStorePosition, labFlatten, labLabel,
    labIsSequence, labStackRemoveConfig]

/-! GH #1027 (bead flapjack-pxn.8.5.14.11): for a relational condition whose
   branches are terminal, `labFlatten` already emits the compact
   original-CakeML shape `[branch, then, label, else]` (the `nr1` case of
   `stack_to_labScript.sml`'s `flatten`).  The remaining byte gap for
   relational conditions is therefore upstream: the production Stack program
   reaches this node with non-terminal branches, which selects the general
   shape with an extra unconditional jump. -/
example :
    labFlatten true 7 1 [] []
      (.ite .less 1 (.imm 10) (.return 2) (.return 3) : StackProg Nat) =
      { lines := [
          labJumpCmp .less 1 (.imm 10) 7 1,
          .labAsm .return [] 0,
          labLabel 7 1,
          .labAsm .return [] 0],
        terminal := true,
        nextLabel := 2 } := by
  simp [labFlatten, labLabel, labJumpCmp, labIsSkip]

/-! GH #1093 (bead flapjack-lhj): the `ite` cases of `labFlatten` must match
   `stack_to_labScript.sml`'s `flatten` (under the port's jump-if-false
   `labBranch` polarity, so `labJumpCmp op` jumps when `op` does *not*
   hold).  The general case must send a true condition to the *then* label
   (previously it targeted the join label, leaving the then-branch dead),
   and the skip-then case must use the negated condition (previously the
   else-branch ran when the condition was true). -/

-- CakeML general case (`p1 ≠ Skip`, `p2 ≠ Skip`, neither terminal):
-- `JumpCmp c → then; ys; Jump join; Label then; xs; Label join`.
example :
    labFlatten false 7 1 [] []
      (.ite .equal 4 (.imm 0) (.arith .add 1 2 3) (.arith .sub 1 2 3) :
        StackProg Nat) =
      { lines := [
          labJumpCmp .notEqual 4 (.imm 0) 7 1,
          .asm (.arith .sub 1 2 3) [] 0,
          labJump 7 2,
          labLabel 7 1,
          .asm (.arith .add 1 2 3) [] 0,
          labLabel 7 2],
        terminal := false,
        nextLabel := 3 } := by
  simp [labFlatten, labLabel, labJump, labJumpCmp, labIsSkip, labNegateCmp]

-- CakeML `p1 = Skip` case: jump over the else-branch when the condition
-- holds; here `labJumpCmp (negate op)` jumps exactly when `op` holds.
example :
    labFlatten false 7 1 [] []
      (.ite .equal 4 (.imm 0) .skip (.arith .add 1 2 3) : StackProg Nat) =
      { lines := [
          labJumpCmp .notEqual 4 (.imm 0) 7 1,
          .asm (.arith .add 1 2 3) [] 0,
          labLabel 7 1],
        terminal := false,
        nextLabel := 2 } := by
  simp [labFlatten, labLabel, labJumpCmp, labIsSkip, labNegateCmp]

-- CakeML `p2 = Skip` case: jump over the then-branch when the condition
-- does not hold; here `labJumpCmp op` jumps exactly when `op` does not hold.
example :
    labFlatten false 7 1 [] []
      (.ite .equal 4 (.imm 0) (.arith .add 1 2 3) .skip : StackProg Nat) =
      { lines := [
          labJumpCmp .equal 4 (.imm 0) 7 1,
          .asm (.arith .add 1 2 3) [] 0,
          labLabel 7 1],
        terminal := false,
        nextLabel := 2 } := by
  simp [labFlatten, labLabel, labJumpCmp, labIsSkip]

-- CakeML `p1 = Skip`, `p2 = Skip` case: no code at all.
example :
    labFlatten false 7 1 [] []
      (.ite .equal 4 (.imm 0) .skip .skip : StackProg Nat) =
      { lines := [], terminal := false, nextLabel := 1 } := by
  simp [labFlatten, labIsSkip]

end Flapjack
