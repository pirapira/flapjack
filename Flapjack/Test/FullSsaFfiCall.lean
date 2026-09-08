import Flapjack.Test.FullSsaPipeline

namespace Flapjack

open RiscV

def fullSsaFfiCallIdBody : Prog (RiscV.Word 64) :=
  .dec "result" .one (.const 0)
    (.seq
      (.extCall "inc" (.var .local "x") (.const 0)
        (.const 0) (.const 0))
      (.return (.var .local "result")))

def fullSsaFfiCallDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "ffiId", inline := false, exported := false,
      params := [("x", .one)], body := fullSsaFfiCallIdBody,
      returnShape := .one },
   .function
    { name := "main", inline := false, exported := false, params := [],
      body := .decCall "answer" .one "ffiId"
        [.const (BitVec.ofNat 64 41)]
        (.return (.var .local "answer")), returnShape := .one }]

def fullSsaFfiCallLinked :
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  compileFlapjackRiscVViaAllocatedStackWithFullSsaLinked .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) [("inc", 7)]
    fullSsaPipelineRemoveConfig fullSsaFfiCallDeclarations

/-! The FFI result is returned in the callee's allocated result register.  In
this example the full-SSA allocator chooses x19 for `result`; unlike the
fixed argument ABI registers, that destination is allocation-dependent. -/
def fullSsaFfiCallHost (register : Nat) : RiscV.WordFfiHost 64 :=
  fun service configuration _ _ _ state =>
    if service = 7 then
      match RiscV.registerOfNat register with
      | some register =>
          some { (RiscV.writeRegister state register (configuration + 1)) with
            pc := state.pc + 4 }
      | none => none
    else none

#guard fullSsaFfiCallLinked.isSome

def fullSsaFfiCallChecked :=
  compileFlapjackRiscVViaAllocatedStackWithFullSsaLinkedChecked .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) [("inc", 7)]
    fullSsaPipelineRemoveConfig fullSsaFfiCallDeclarations

#guard staticResultOk fullSsaFfiCallChecked
#guard match fullSsaFfiCallChecked.1 with
  | .ok (some _) => true
  | _ => false

def fullSsaFfiCallInvalidDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := false, params := [],
      body := .return (.const (BitVec.ofNat 64 7)),
      returnShape := .comb [.one, .one] }]

def fullSsaFfiCallInvalidChecked :=
  compileFlapjackRiscVViaAllocatedStackWithFullSsaLinkedChecked .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) []
    fullSsaPipelineRemoveConfig fullSsaFfiCallInvalidDeclarations

#guard !(staticResultOk fullSsaFfiCallInvalidChecked)

def fullSsaFfiCallLookupEntry (label : Nat) :
    List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64)) →
      Option (RiscV.Word 64)
  | [] => none
  | (candidate, entry, _) :: sections =>
      if candidate == label then some entry
      else fullSsaFfiCallLookupEntry label sections

def fullSsaFfiCallMachineResult : Option (List (RiscV.Word 64)) := do
  let sections ← fullSsaFfiCallLinked
  let entry ← fullSsaFfiCallLookupEntry 2 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  RiscV.executeFunctionAtWithFfi (fullSsaFfiCallHost 19) 4000 0 entry 276 [] image [2] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 276)

def fullSsaFfiCallSourceFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("ffiId", ["x"], fullSsaFfiCallIdBody)]

def fullSsaFfiCallSourceMain : Prog (RiscV.Word 64) :=
  .decCall "answer" .one "ffiId"
    [.const (BitVec.ofNat 64 41)]
    (.return (.var .local "answer"))

def fullSsaFfiCallSourceHandler : PanFfiHandler (RiscV.Word 64) :=
  fun function configuration _ _ _ locals =>
    if function == "inc" then
      some (updatePanLocal locals "result" (configuration + 1))
    else none

theorem fullSsaFfiCall_machine_execution :
    fullSsaFfiCallMachineResult = some [BitVec.ofNat 64 42] := by
  native_decide

theorem fullSsaFfiCall_source_execution :
  (evalPanProgWithCallsAndFfi fullSsaFfiCallSourceFunctions
    fullSsaFfiCallSourceHandler 30
    (fun _ => none) fullSsaFfiCallSourceMain).map (fun result =>
      match result with
      | .returned _ values => values
      | _ => []) = some [BitVec.ofNat 64 42] := by
  decide +kernel

theorem fullSsaFfiCall_source_machine_agreement :
    (evalPanProgWithCallsAndFfi fullSsaFfiCallSourceFunctions
      fullSsaFfiCallSourceHandler 30
      (fun _ => none) fullSsaFfiCallSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = some [BitVec.ofNat 64 42] ∧
      fullSsaFfiCallMachineResult = some [BitVec.ofNat 64 42] :=
  ⟨fullSsaFfiCall_source_execution, fullSsaFfiCall_machine_execution⟩

/-! This equality exposes the complete declaration-call simulation directly:
    source argument binding and FFI execution agree with the linked RISC-V
    call entry, allocated FFI result register, and return continuation. -/

theorem fullSsaFfiCall_source_machine_simulation :
    (evalPanProgWithCallsAndFfi fullSsaFfiCallSourceFunctions
      fullSsaFfiCallSourceHandler 30
      (fun _ => none) fullSsaFfiCallSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) =
      fullSsaFfiCallMachineResult := by
  calc
    _ = some [BitVec.ofNat 64 42] := fullSsaFfiCall_source_execution
    _ = _ := fullSsaFfiCall_machine_execution.symm

end Flapjack
