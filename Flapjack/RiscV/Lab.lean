import Flapjack.Lab
import Flapjack.RiscV.Ffi

/-!
# LabLang to RISC-V

This module is the first concrete assembler boundary after StackLang
flattening. It computes byte positions for local labels, resolves symbolic
jumps, and lowers the LabLang operations supported by the current RISC-V
model. Unsupported target operations fail through Option rather than being
silently emitted.
-/

namespace Flapjack.RiscV

def labConditionPreludeCount (operator : Cmp)
    (right : WordRegImm (Word width)) : Nat :=
  match right with
  | .reg _ => match operator with | .test | .notTest => 1 | _ => 0
  | .imm value =>
      if value == 0 then
        match operator with | .test | .notTest => 1 | _ => 0
      else 1

def labLineInstructionCount : LabLine (Word width) → Nat
  | .label _ _ _ => 0
  | .asm _ _ _ => 1
  | .labAsm operation _ _ =>
      match operation with
      | .jump _ | .call _ | .locValue _ _ | .install | .halt => 1
      | .jumpCmp operator _ right _ => 1 + labConditionPreludeCount operator right
      | .callFfi _ => 2

def labCollectLabels (_sectionId : Nat) (position : Nat) :
    List (LabLine (Word width)) → List (Nat × Nat)
  | [] => []
  | .label _ label _ :: lines =>
      (label, position) :: labCollectLabels _sectionId position lines
  | line :: lines =>
      labCollectLabels _sectionId
        (position + 4 * labLineInstructionCount line) lines

def labLookupPosition (label : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (candidate, position) :: labels =>
      if label == candidate then some position
      else labLookupPosition label labels

def labResolveRef (sectionId : Nat) (labels : List (Nat × Nat)) (ref : LabRef) :
    Option Nat :=
  if ref.sectionId == sectionId then labLookupPosition ref.label labels
  else none

def labOffset [NeZero width] (target position : Nat) : Word width :=
  if target >= position then
    BitVec.ofNat width (target - position)
  else
    0 - BitVec.ofNat width (position - target)

def labBranch [NeZero width] (operator : Cmp) (left right : Fin 32)
    (offset : Word width) : Instruction width :=
  match operator with
  | .equal => .branchNe left right offset
  | .notEqual => .branchEq left right offset
  | .less => .branchGe left right offset
  | .notLess => .branchLt left right offset
  | .lower => .branchGeU left right offset
  | .notLower => .branchLtU left right offset
  | .test => .branchNe left right offset
  | .notTest => .branchEq left right offset

def labCompilePlain [NeZero width] :
    LabPlain (Word width) → Option (List (Instruction width))
  | .word instruction => (wordInstToInstruction instruction).map List.singleton
  | .const destination value => do
      let destination ← registerOfNat destination
      pure [.addi destination 0 (BitVec.ofNat width value)]
  | .tick => pure [.addi 0 0 0]
  | .jumpReg register => do
      let register ← registerOfNat register
      pure [.jalr 0 register 0]
  | .shareMem operator register address =>
      wordShareInstToInstructions operator register (.var address)
  | .codeBufferWrite _ _ => none

def labCompileAsm [NeZero width] (context : WordFfiContext)
    (sectionId : Nat) (labels : List (Nat × Nat)) (position : Nat) :
    LabAsm (Word width) → Option (List (Instruction width))
  | .jump target => do
      let target ← labResolveRef sectionId labels target
      pure [.jal 0 (labOffset target position)]
  | .call target => do
      let target ← labResolveRef sectionId labels target
      pure [.jal 1 (labOffset target position)]
  | .locValue register target => do
      let register ← registerOfNat register
      let target ← labResolveRef sectionId labels target
      pure [.addi register 0 (BitVec.ofNat width target)]
  | .jumpCmp operator condition right target => do
      let (left, right, prelude) ← wordConditionOperands operator condition right
      let target ← labResolveRef sectionId labels target
      let branchPosition := position + 4 * prelude.length
      pure (prelude ++ [labBranch operator left right
        (labOffset target branchPosition)])
  | .callFfi function => do
      let service ← lookupWordFfiService function context.services
      pure [.addi 14 0 (BitVec.ofNat width service), .ecall]
  | .install | .halt => none

def labCompileLines [NeZero width] (context : WordFfiContext)
    (sectionId : Nat) (labels : List (Nat × Nat)) (position : Nat) :
    List (LabLine (Word width)) → Option (List (Instruction width))
  | [] => some []
  | .label _ _ _ :: lines =>
      labCompileLines context sectionId labels position lines
  | .asm operation _ _ :: lines => do
      let code ← labCompilePlain operation
      let rest ← labCompileLines context sectionId labels
        (position + 4 * labLineInstructionCount (.asm operation [] 0)) lines
      pure (code ++ rest)
  | .labAsm operation _ _ :: lines => do
      let code ← labCompileAsm context sectionId labels position operation
      let rest ← labCompileLines context sectionId labels
        (position + 4 * labLineInstructionCount (.labAsm operation [] 0)) lines
      pure (code ++ rest)

def compileLabSection [NeZero width] (context : WordFfiContext)
    (sectionData : LabSection (Word width)) : Option (List (Instruction width)) :=
  let labels := labCollectLabels sectionData.name 0 sectionData.lines
  labCompileLines context sectionData.name labels 0 sectionData.lines

theorem labLineInstructionCount_ffi :
    labLineInstructionCount
        (.labAsm (.callFfi "sum") [] 0 : LabLine (Word width)) = 2 := by
  rfl

theorem compileLabSection_ffi [NeZero width] :
    compileLabSection { services := [("sum", 7)] }
      ⟨2, [
        .labAsm (.callFfi "sum") [] 0]⟩ =
      some [.addi 14 0 (BitVec.ofNat width 7), .ecall] := by
  simp [compileLabSection, labCollectLabels, labCompileLines,
    labLineInstructionCount, labCompileAsm, lookupWordFfiService]

end Flapjack.RiscV
