import Flapjack.RiscV.LabDiagnostics
import Flapjack.RiscV.InitializedRuntime
import Flapjack.RiscV.Encoding
import Flapjack.Compiler.Backend.LabToTarget.Compile
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

/-!
# Executed Lab-to-target route through the reviewed `lab_to_target$compile`

The executed RV64 image is produced by the reviewed
`LabToTarget.compile` (`lab_to_target$compile_def`: `filter_skip`,
`remove_labels`, `prog_to_bytes`, `get_shmem_info` and the configuration
update) with the exact native `riscv_config` and the original
`riscv_lab_conf`. The executed Lab program is decoded to the native section
carrier by the existing `ExecutedCodec.programFromExecuted?`; a codec failure is
a lowering failure. The output sections are the byte ranges recorded by the
original `sec_pos_len` (`get_symbols`) of the returned configuration.

Other word widths keep the existing stored-length linker, for which no native
`riscv_config` exists.
-/

namespace Flapjack.RiscV

open Flapjack.Compiler.Backend

/-- The literal `riscv_lab_conf` quotation of `riscv_configScript.sml:54`
(`<|pos:=0; ffi_names:=NONE; labels:=LN; sec_pos_len:=[]; init_clock:=5;
hash_size:=104729n; shmem_extra:=[]|>`), the `lab_conf` field of
`riscv_backend_config_def`. An SML value, not a HOL declaration, so the
projection is untagged. -/
def riscvLabConf : LabToTarget.Config :=
  { labels := .ln, secPosLen := [], pos := 0, initClock := 5, ffiNames := none,
    shmemExtra := [], hashSize := 104729 }

/-- Split the reviewed `lab_to_target` byte image into the sections recorded by
its `sec_pos_len` (Flapjack output adapter; no HOL original). -/
def sectionsOfSymbols {width : Nat} [NeZero width] (bytes : List (BitVec 8)) :
    List (Nat × Nat × Nat) → List (EncodedRiscVSection width)
  | [] => []
  | (label, position, length) :: rest =>
      { label, address := BitVec.ofNat width position,
        bytes := (bytes.drop position).take length } :: sectionsOfSymbols bytes rest

/-- RV64 Lab-to-target through the reviewed `LabToTarget.compile` with the
native `riscv_config` and `riscv_lab_conf`; returns the reviewed byte image and
configuration. Codec failure and HOL's `NONE` are both `none`. -/
def labToTargetRiscV (program : LabProgram (Word 64)) :
    Option (List (BitVec 8) × LabToTarget.Config) := do
  let native ← StackToLab.ExecutedCodec.programFromExecuted? program
  LabToTarget.compile Compiler.Encoders.RiscV.Target.riscvConfig riscvLabConf native

/-- Executed sections of a Lab program: at width 64 the reviewed
`labToTargetRiscV` image split by its `sec_pos_len`; at other widths the
existing stored-length linker and instruction encoder. -/
def labProgramToRiscVSections {width : Nat} [NeZero width] (context : WordFfiContext)
    (program : LabProgram (Word width)) : Option (List (EncodedRiscVSection width)) :=
  if h : width = 64 then by
    subst h
    exact (labToTargetRiscV program).map fun (bytes, config) =>
      sectionsOfSymbols bytes config.secPosLen
  else
    (compileLabProgramLinkedWithNativeInitialization context program).map encodeLinkedSections

/-- At width 64 the executed bytes are exactly the reviewed
`lab_to_target$compile` image (Flapjack routing fact; no HOL original). -/
theorem labProgramToRiscVSections_rv64 (context : WordFfiContext)
    (program : LabProgram (Word 64)) :
    labProgramToRiscVSections context program =
      (labToTargetRiscV program).map fun (bytes, config) =>
        sectionsOfSymbols bytes config.secPosLen := by
  simp [labProgramToRiscVSections]

/-- Executed Stack-to-RISC-V sections: the native Stack-to-Lab composition of
`initializedRuntimeLab?` followed by `labProgramToRiscVSections`. Arguments and
error behaviour match
`compileStackProgramNatListLinkedWithSimpleGcAndStoreConstsToRiscVCakeChecked`. -/
def compileStackProgramNatListToRiscVSectionsCakeChecked
    [NeZero width] (context : WordFfiContext) (removeConfig : StackRemoveConfig)
    (_allocConfig : StackAllocConfig) (_gcConfig : StackGcConfig)
    (_storeConstsLocation registerCount : Nat)
    (entryLabel _initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) :
    Except LabLoweringError (List (EncodedRiscVSection width)) :=
  if entryLabel ≠ 0 || removeConfig.bytesInWord ≠ width / 8 then
    .error { sectionId := 0, position := 0, feature := .loweringFailure }
  else
    let removeConfig := cakeStackRemoveConfig removeConfig
    let bounds := (BitVec.ofInt width (-2048), BitVec.ofNat width 2047)
    match initializedRuntimeLab? removeConfig.jump bounds
        removeConfig.stackPointer stackFunctionFirstLabel registerCount programs with
    | none => .error { sectionId := 0, position := 0, feature := .loweringFailure }
    | some lab => match labProgramToRiscVSections context lab with
      | some sections => .ok sections
      | none => .error { sectionId := 0, position := 0, feature := .loweringFailure }

end Flapjack.RiscV
