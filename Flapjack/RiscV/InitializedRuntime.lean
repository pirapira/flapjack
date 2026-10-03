import Flapjack.Compiler.Backend.StackAlloc.Compile
import Flapjack.Compiler.Backend.StackRawCall
import Flapjack.Compiler.Backend.WordToStack.NativeStubs
import Flapjack.RiscV.Lab
import Flapjack.Compiler.Backend.StackToLab.RuntimeLabels
import Flapjack.Compiler.Backend.DataToWord.MaxHeapLimit
import Flapjack.Compiler.Backend.LabFilter
import Flapjack.Compiler.Backend.LabToTarget.Encoding
import Flapjack.Compiler.Backend.LabToTarget.Labels
import Flapjack.Compiler.Encoders.RiscV.Target

/-! Executed runtime initialization infrastructure, with no standalone HOL
original. This uses the reviewed whole StackRemove/native naming/section
composition and derives all relocation labels from its actual output. The
legacy fixed runtime table is not a source for this linker.
-/
namespace Flapjack.RiscV

/-- Literal data component of original riscv_configScript.sml:51, an SML
quotation used by riscv_backend_config_def, with the actual Pancake no-GC
override from compilerScript.sml:744–747. This is its data-field projection,
not a tagged port of the whole backend configuration update. -/
def initializedRuntimeDataConfig : Flapjack.Compiler.Backend.DataToWord.Config :=
  { tagBits := 4, lenBits := 4, padBits := 2, lenSize := 32,
    hasDiv := true, hasLongdiv := false, hasFpOps := false, hasFpTern := false,
    be := false, callEmptyFfi := false, gcKind := .none }

/-- RV64 Pancake runtime composition, including the original three entry stubs.
The source bodies are the Word-to-Stack function sections, before any stack
allocation. Global labels are injectively normalized to the original namespace
and the native Raise and StoreConsts stubs are prepended, as Word-to-Stack does.
Then, exactly as `stack_to_lab$compile_def`, the tagged native
`stack_rawcall$compile`, `stack_alloc$compile` (with Pancake's `GC = None`
data configuration), `stack_remove$compile` and `stack_names$compile` run on the
whole list before `prog_to_section`. Section codecs fail explicitly; this
boundary is not a simulation theorem for the upstream passes. -/
def initializedRuntimeLab? {width : Nat} [NeZero width]
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start registerCount : Nat)
    (programs : List (Nat × StackProg Nat)) : Option (LabProgram (Word width)) := do
  let native ← Flapjack.Compiler.Backend.StackToLab.InitializedProduction.nativeInputs? programs
  let source := Flapjack.Compiler.Backend.StackToLab.RuntimeLabels.originalInputs
    (native.filter (fun entry => entry.1 >= 3))
  let support :=
    [(Flapjack.raiseStubLocation, Flapjack.Compiler.Backend.WordToStack.Native.raiseStubNative false registerCount),
     (Flapjack.storeConstsStubLocation, Flapjack.Compiler.Backend.WordToStack.Native.storeConstsStubNative registerCount)]
  let native := Flapjack.Compiler.Backend.StackAlloc.compile
    initializedRuntimeDataConfig
    (Flapjack.Compiler.Backend.StackRawCall.compile (support ++ source))
  let heap := 2 * Flapjack.Compiler.Backend.DataToWord.maxHeapLimit width
    initializedRuntimeDataConfig - 1
  Flapjack.Compiler.Backend.StackToLab.InitializedProduction.compileNative?
    jump bounds false heap pointer
    (Flapjack.Compiler.Backend.StackToLab.RuntimeLabels.originalSection start)
    Flapjack.Compiler.Backend.RiscVConfig.riscvNames native

/-- Successful output of the actual runtime-image lowering decodes to the
literal native section composition. Every converted source section, native
support stub, allocation pass, initializer argument and naming map is retained.
This untagged theorem is Flapjack codec infrastructure with no standalone HOL
original; codec success is not a target-run assumption or pass simulation. -/
theorem initializedRuntimeLab_recover {width : Nat} [NeZero width]
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start registerCount : Nat)
    (programs : List (Nat × StackProg Nat)) (outputs : LabProgram (Word width))
    (accepted : initializedRuntimeLab? jump bounds pointer start registerCount programs = some outputs) :
    ∃ converted,
      Flapjack.Compiler.Backend.StackToLab.InitializedProduction.nativeInputs? programs = some converted ∧
      let source := Flapjack.Compiler.Backend.StackToLab.RuntimeLabels.originalInputs
        (converted.filter (fun entry => entry.1 >= 3))
      let support :=
        [(Flapjack.raiseStubLocation, Flapjack.Compiler.Backend.WordToStack.Native.raiseStubNative false registerCount),
         (Flapjack.storeConstsStubLocation, Flapjack.Compiler.Backend.WordToStack.Native.storeConstsStubNative registerCount)]
      let allocated := Flapjack.Compiler.Backend.StackAlloc.compile
        initializedRuntimeDataConfig
        (Flapjack.Compiler.Backend.StackRawCall.compile (support ++ source))
      let heap := 2 * Flapjack.Compiler.Backend.DataToWord.maxHeapLimit width
        initializedRuntimeDataConfig - 1
      Flapjack.Compiler.Backend.StackToLab.ExecutedCodec.mapCodec?
        Flapjack.Compiler.Backend.StackToLab.ExecutedCodec.sectionFromExecuted? outputs = some
          ((Flapjack.Compiler.Backend.StackNames.compileHOL
            Flapjack.Compiler.Backend.RiscVConfig.riscvNames
            (Flapjack.Compiler.Backend.StackRemove.compileHOL jump bounds false heap pointer
              (Flapjack.Compiler.Backend.StackToLab.RuntimeLabels.originalSection start)
              allocated)).map Flapjack.Compiler.Backend.StackToLab.progToSectionHOL) := by
  cases convertedEq :
      Flapjack.Compiler.Backend.StackToLab.InitializedProduction.nativeInputs?
        (width := width) programs with
  | none => simp [initializedRuntimeLab?, convertedEq] at accepted
  | some converted =>
      refine ⟨converted, rfl, ?_⟩
      have lowered := accepted
      simp only [initializedRuntimeLab?, convertedEq] at lowered
      exact Flapjack.Compiler.Backend.StackToLab.InitializedProduction.compileNative_recover
        _ _ _ _ _ _ _ _ _ lowered

/-- Executable label-index adapter, with no HOL original. The reviewed native
label computation decides duplicate-label and duplicate-section precedence;
the tree enumeration only materializes the existing executable lookup index.
Unsupported legacy-only lines fail at the native codec boundary. -/
def initializedRuntimeLabelIndex? [NeZero width]
    (program : LabProgram (Word width)) : Option LabLabelIndex := do
  let native ← Flapjack.Compiler.Backend.StackToLab.ExecutedCodec.programFromExecuted? program
  let labels := Flapjack.Compiler.Backend.LabToTarget.computeLabelsAlt 0 native .ln
  let entries := (Flapjack.sptToAList labels).flatMap fun (sectionId, sectionLabels) =>
    (Flapjack.sptToAList sectionLabels).map fun (label, position) =>
      (sectionId, label, position)
  pure (labLabelIndexOf entries)

/-- Actual RV64 initial encoding uses the complete reviewed source encoder and
`filterSkip` followed by `encSecList`, retaining offset-zero encodings and the
resulting source lengths. Relocation can make those stored bytes stale; executed
consumers ignore them and re-encode at the actual offset. Other
word widths retain the existing non-RV64 infrastructure; no source RV64 encoder
or cross-language equivalence is asserted for that path. This adapter has no
standalone HOL original. -/
def initializedRuntimeInitialStoredProgram? [NeZero width]
    (program : LabProgram (Word width)) : Option (LabProgram (Word width)) := do
  if sameWidth : width = 64 then
    let native ← Flapjack.Compiler.Backend.StackToLab.ExecutedCodec.programFromExecuted? program
    let encoder := fun instruction : Flapjack.Compiler.Encoders.Asm.HolAsm width =>
      Flapjack.Compiler.Encoders.RiscV.Target.riscvEnc (sameWidth ▸ instruction)
    Flapjack.Compiler.Backend.StackToLab.ExecutedCodec.programToExecuted?
      (Flapjack.Compiler.Backend.LabToTarget.encSecList encoder
        (Flapjack.Compiler.Backend.LabFilter.filterSkip native))
  else
    pure (labInitialStoredProgram program)

/-- Stored-length convergence over the complete actual program. Exhausting the
relocation budget fails, matching HOL `remove_labels_loop`; an unconverged
program must never reach instruction lowering. -/
def initializedRuntimeEncodeStable [NeZero width] (fuel : Nat)
    (context : WordFfiContext) (haltPc : Nat) (program : LabProgram (Word width)) :
    Option (LabProgram (Word width)) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      let labels ← initializedRuntimeLabelIndex? program
      let next := labEncodeStoredProgram context labels 0 0 haltPc program
      if labStoredLineLengths next == labStoredLineLengths program then pure next
      else initializedRuntimeEncodeStable fuel context haltPc next

/-- Both relocation sweeps retain original maximum observed instruction slots;
all entry/GC/raise/store/source labels come from the generated program. -/
def compileLabProgramLinkedWithNativeInitialization [NeZero width]
    (context : WordFfiContext) (program : LabProgram (Word width)) :
    Option (List (Nat × Word width × List (Instruction width))) := do
  let initial ← initializedRuntimeInitialStoredProgram? program
  let encoded ← initializedRuntimeEncodeStable 8 context (labStoredProgramLength initial) initial
  let relabelled := labUpdateStoredLabelLengths 0 encoded
  let final ← initializedRuntimeEncodeStable 8 context (labStoredProgramLength relabelled) relabelled
  let labels ← initializedRuntimeLabelIndex? final
  compileLabProgramLinkedWithStoredLengthsAux context labels 0 0
    (labStoredProgramLength final) final

end Flapjack.RiscV
