import Flapjack.RiscV.PipelineDiagnostics

namespace Flapjack

open RiscV

def pipelineDiagnosticsConfig : WordStackConfig :=
  { locations := [(0, .register 5), (1, .register 6),
      (2, .register 7), (3, .register 8)]
    scratch := 31
    stackBase := 10 }

example :
    RiscV.pipelineWordFunctionsToStackChecked (width := 64)
      [(17, [], (.alloc 0 ([], []) : WordProg (RiscV.Word 64)))] =
        .error { sectionId := 17, path := [], feature := .alloc } := by
  simp [RiscV.pipelineWordFunctionsToStackChecked,
    RiscV.wordStackIdentityConfig, RiscV.wordToStackProgWordChecked,
    RiscV.wordToStackProgNatChecked, RiscV.wordToStackProgNat,
    RiscV.wordProgFirstUnsupported, RiscV.wordProgToNat]

example :
    RiscV.pipelineWordFunctionsToStackChecked (width := 64)
      [(23, [], ((.seq .skip (.storeConsts 0 1 2 3 [])) :
        WordProg (RiscV.Word 64)))] =
        .error { sectionId := 23, path := [1], feature := .storeConsts } := by
  simp [RiscV.pipelineWordFunctionsToStackChecked,
    RiscV.wordStackIdentityConfig, RiscV.wordToStackProgWordChecked,
    RiscV.wordToStackProgNatChecked, RiscV.wordToStackProgNat,
    RiscV.wordProgFirstUnsupported, RiscV.wordProgToNat]

example :
    RiscV.compileLabProgramChecked (width := 64) { services := [] }
      [⟨17, [.labAsm (.heapAlloc 3) [] 0]⟩] =
        .error { sectionId := 17, position := 0, feature := .heapAlloc } := by
  rfl

example :
    RiscV.compileLabProgramChecked (width := 64) { services := [] }
      [⟨29, [.asm (.word (.arith (.longDiv 0 3 3 0 6))) [] 0]⟩] =
        .error { sectionId := 29, position := 0, feature := .longDiv } := by
  rfl

example :
    RiscV.compileLabProgramChecked (width := 64) { services := [] }
      [⟨19, [.asm (.const 1 7) [] 0]⟩] =
        .ok [.addi 1 0 (BitVec.ofNat 64 7)] := by
  rfl

example :
    RiscV.compileLabProgramChecked (width := 64) { services := [] }
      [⟨1, [.labAsm (.jump ⟨2, 0⟩) [] 0]⟩,
       ⟨2, [.label 2 0 0, .asm (.const 1 7) [] 0]⟩] =
        .ok [.jal 0 (BitVec.ofNat 64 4),
          .addi 1 0 (BitVec.ofNat 64 7)] := by
  rfl

def checkedPipelineDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]

def checkedPipelineRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

#guard
    (compileFlapjackRiscVViaStackChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      checkedPipelineRemoveConfig checkedPipelineDeclarations).isOk

#guard
    (compileFlapjackRiscVViaStackBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
      checkedPipelineRemoveConfig checkedPipelineDeclarations).isOk

#guard
    match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" "fun main() { return 7; }" with
    | .ok artifact => artifact.bytes.length > 0
    | .error _ => false

#guard
    match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" "fun main() {" with
    | .error (.parse _) => true
    | _ => false

#guard
    match compileFlapjackRiscVSourceImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" "fun main() { return 7; }" with
    | .ok image => image.sections.length > 0 &&
        image.sections.all (fun entry => entry.bytes.length % 4 == 0)
    | .error _ => false

#guard
    match compileFlapjackRiscVSourceImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "missing" "fun main() { return 7; }" with
    | .error .entryNotFound => true
    | _ => false

#guard
    match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" "fun main() { return 7; }" with
    | .ok image => image.bitmaps.data.length > 0 && image.sections.length > 0 &&
        image.sections.all (fun entry => entry.bytes.length % 4 == 0)
    | .error _ => false

end Flapjack
