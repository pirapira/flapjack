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
  | longDiv
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

def labPlainUnsupportedFeature [NeZero width] :
    LabPlain (Word width) → Option LabUnsupportedFeature
  | .word (.arith (.longDiv _ _ _ _ _)) => some .longDiv
  | _ => none

def labPlainLoweringError [NeZero width] (sectionId position : Nat)
    (operation : LabPlain (Word width)) : LabLoweringError :=
  { sectionId, position,
    feature := (labPlainUnsupportedFeature operation).getD .loweringFailure }

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
      | none => .error (labPlainLoweringError sectionId position operation)
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

def labCompileAsmProgramChecked [NeZero width] (context : WordFfiContext)
    (sectionId : Nat) (labels : List (Nat × Nat × Nat)) (position : Nat)
    (operation : LabAsm (Word width)) :
    Except LabLoweringError (List (Instruction width)) :=
  match operation with
  | .heapAlloc _ => .error (labLoweringError sectionId position .heapAlloc)
  | .halt => .error (labLoweringError sectionId position .halt)
  | operation =>
      match labCompileAsmProgram context labels position operation with
      | some code => .ok code
      | none => .error (labLoweringError sectionId position .loweringFailure)

/-! Program-level checked lowering keeps the same global-label and byte-offset
    calculation as `compileLabProgram`, but retains the first section and
    source position at which lowering fails. -/
def labCompileProgramLinesChecked [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (sectionId : Nat) (position : Nat) :
    List (LabLine (Word width)) →
      Except LabLoweringError (List (Instruction width))
  | [] => .ok []
  | .label _ _ _ :: lines =>
      labCompileProgramLinesChecked context labels sectionId position lines
  | .asm operation _ _ :: lines =>
      match labCompilePlain operation with
      | none => .error (labPlainLoweringError sectionId position operation)
      | some code =>
          match labCompileProgramLinesChecked context labels sectionId
              (position + 4 * labLineInstructionCount (.asm operation [] 0)) lines with
          | .error error => .error error
          | .ok rest => .ok (code ++ rest)
  | .labAsm operation _ _ :: lines =>
      match labCompileAsmProgramChecked context sectionId labels position operation with
      | .error error => .error error
      | .ok code =>
          match labCompileProgramLinesChecked context labels sectionId
              (position + 4 * labLineInstructionCount (.labAsm operation [] 0)) lines with
          | .error error => .error error
          | .ok rest => .ok (code ++ rest)

def labCompileProgramSectionsChecked [NeZero width] (context : WordFfiContext)
    (labels : List (Nat × Nat × Nat)) (base : Nat) :
    LabProgram (Word width) →
      Except LabLoweringError (List (Instruction width))
  | [] => .ok []
  | sectionData :: sections =>
      match labCompileProgramLinesChecked context labels sectionData.name base
          sectionData.lines with
      | .error error => .error error
      | .ok code =>
          match labCompileProgramSectionsChecked context labels
              (base + 4 * labSectionInstructionCount sectionData) sections with
          | .error error => .error error
          | .ok rest => .ok (code ++ rest)

def compileLabProgramChecked [NeZero width] (context : WordFfiContext)
    (program : LabProgram (Word width)) :
    Except LabLoweringError (List (Instruction width)) :=
  let labels := labCollectProgramLabels 0 program
  labCompileProgramSectionsChecked context labels 0 program

/-! Checked linked lowering.  The section-entry metadata is identical to the
historical linker; only the per-section compiler is replaced by the checked
version so a failing section and byte position survive the API boundary. -/
def labCompileProgramLinkedAuxChecked [NeZero width]
    (context : WordFfiContext) (labels : List (Nat × Nat × Nat))
    (base : Nat) : LabProgram (Word width) →
      Except LabLoweringError
        (List (Nat × Word width × List (Instruction width)))
  | [] => .ok []
  | sectionData :: sections =>
      match labCompileProgramLinesChecked context labels sectionData.name base
          sectionData.lines with
      | .error error => .error error
      | .ok code =>
          match labCompileProgramLinkedAuxChecked context labels
              (base + 4 * labSectionInstructionCount sectionData) sections with
          | .error error => .error error
          | .ok rest =>
              .ok ((sectionData.name, BitVec.ofNat width base, code) :: rest)

def compileLabProgramLinkedChecked [NeZero width]
    (context : WordFfiContext) (program : LabProgram (Word width)) :
    Except LabLoweringError
      (List (Nat × Word width × List (Instruction width))) :=
  let labels := labCollectProgramLabels 0 program
  labCompileProgramLinkedAuxChecked context labels 0 program

def compileStackProgramNatListToRiscVChecked [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Except LabLoweringError (List (Instruction width)) :=
  match stackProgramsWithLongDivRuntime config programs with
  | none => .error { sectionId := 0, position := 0, feature := .loweringFailure }
  | some programs =>
      compileLabProgramChecked context
        ((programs.map (fun (sectionId, program) =>
          if sectionId = cakeLongDiv1Location ||
              sectionId = cakeLongDivLocation then
            labProgramToEntrySection sectionId 0 initialLabel
              (stackRemoveComplete config program)
          else
            labProgramToEntrySection sectionId entryLabel initialLabel
              (stackRemoveComplete config program))).map labSectionNatToWord)

def compileStackProgramNatListWithRaiseStubToRiscVChecked [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Except LabLoweringError (List (Instruction width)) :=
  compileStackProgramNatListToRiscVChecked context config entryLabel initialLabel
    ((stackRaiseStubLocation, stackRaiseStub false config.addressScratch) :: programs)

def compileStackProgramNatListLinkedWithRaiseStubToRiscVChecked [NeZero width]
    (context : WordFfiContext) (config : StackRemoveConfig)
    (entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Except LabLoweringError
      (List (Nat × Word width × List (Instruction width))) :=
  match stackProgramsWithLongDivRuntime config
      ((stackRaiseStubLocation, stackRaiseStub false config.addressScratch) :: programs) with
  | none => .error { sectionId := 0, position := 0, feature := .loweringFailure }
  | some programs =>
      compileLabProgramLinkedChecked context
        (((programs.map (fun (sectionId, program) =>
          if sectionId = cakeLongDiv1Location ||
              sectionId = cakeLongDivLocation then
            labProgramToEntrySection sectionId 0 initialLabel
              (stackRemoveComplete config program)
          else
            labProgramToEntrySection sectionId entryLabel initialLabel
              (stackRemoveComplete config program))).map labSectionNatToWord))

def compileStackProgramNatToRiscVChecked [NeZero width]
  (context : WordFfiContext) (config : StackRemoveConfig)
    (sectionId initialLabel : Nat) (program : StackProg Nat) :
    Except LabLoweringError (List (Instruction width)) :=
  match stackProgramsWithLongDivRuntime config [(sectionId, program)] with
  | none => .error { sectionId := sectionId, position := 0, feature := .loweringFailure }
  | some programs =>
      compileLabProgramChecked context
        ((programs.map (fun (runtimeSection, runtimeProgram) =>
          if runtimeSection = cakeLongDiv1Location ||
              runtimeSection = cakeLongDivLocation then
            labProgramToEntrySection runtimeSection 0 initialLabel
              (stackRemoveComplete config runtimeProgram)
          else
            labProgramToSectionAfterStackRemove config runtimeSection initialLabel
              runtimeProgram)).map labSectionNatToWord)

end Flapjack.RiscV
