import Flapjack.RiscV.Lab

/-!
# Checked Lab-to-RISC-V diagnostics

The historical Lab compiler returns `Option` so existing callers keep their
pass-local API.  That loses the reason and source position when a target-only
pseudo-operation is outside the current RISC-V runtime contract.  This module
adds a checked boundary with a structured, section/position-tagged error while
leaving the established Option entrypoints unchanged.
-/

namespace Flapjack.RiscV

inductive LabUnsupportedFeature where
  | heapAlloc
  | halt
  | loweringFailure
  deriving DecidableEq, Repr

structure LabLoweringError where
  sectionId : Nat
  position : Nat
  feature : LabUnsupportedFeature
  deriving DecidableEq, Repr

def labLoweringError (sectionId position : Nat)
    (feature : LabUnsupportedFeature) : LabLoweringError :=
  { sectionId, position, feature }

def labCompileAsmChecked [NeZero width] (context : WordFfiContext)
    (sectionId : Nat) (labels : List (Nat × Nat)) (position : Nat)
    (operation : LabAsm (Word width)) :
    Except LabLoweringError (List (Instruction width)) :=
  match operation with
  | .heapAlloc _ => .error (labLoweringError sectionId position .heapAlloc)
  | .halt => .error (labLoweringError sectionId position .halt)
  | operation =>
      match labCompileAsm context sectionId labels position operation with
      | some code => .ok code
      | none => .error (labLoweringError sectionId position .loweringFailure)

def labCompileLinesChecked [NeZero width] (context : WordFfiContext)
    (sectionId : Nat) (labels : List (Nat × Nat)) (position : Nat) :
    List (LabLine (Word width)) →
      Except LabLoweringError (List (Instruction width))
  | [] => .ok []
  | .label _ _ _ :: lines =>
      labCompileLinesChecked context sectionId labels position lines
  | .asm operation _ _ :: lines =>
      match labCompilePlain operation with
      | none => .error (labLoweringError sectionId position .loweringFailure)
      | some code =>
          match labCompileLinesChecked context sectionId labels
              (position + 4 * labLineInstructionCount (.asm operation [] 0)) lines with
          | .error error => .error error
          | .ok rest => .ok (code ++ rest)
  | .labAsm operation _ _ :: lines =>
      match labCompileAsmChecked context sectionId labels position operation with
      | .error error => .error error
      | .ok code =>
          match labCompileLinesChecked context sectionId labels
              (position + 4 * labLineInstructionCount (.labAsm operation [] 0)) lines with
          | .error error => .error error
          | .ok rest => .ok (code ++ rest)

def compileLabSectionChecked [NeZero width] (context : WordFfiContext)
    (sectionData : LabSection (Word width)) :
    Except LabLoweringError (List (Instruction width)) :=
  let labels := labCollectLabels sectionData.name 0 sectionData.lines
  labCompileLinesChecked context sectionData.name labels 0 sectionData.lines

def compileStackProgramNatToRiscVChecked [NeZero width]
  (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel : Nat) (program : StackProg Nat) :
    Except LabLoweringError (List (Instruction width)) :=
  compileLabSectionChecked context
    (labSectionNatToWord
      (labProgramToSectionAfterStackRemove config sectionId initialLabel program))

end Flapjack.RiscV
