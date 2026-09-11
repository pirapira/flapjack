import Flapjack.Test.FullSsaPipeline
import Flapjack.CrepeSemantics
import Flapjack.LoopSemantics

namespace Flapjack

open RiscV

def fullSsaHandlerFfiRemoveConfig : StackRemoveConfig :=
  { storeBase := 25, currHeap := 26, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

/-! Combined full-SSA handler/FFI regression.  The callee performs a stateful
    external call, then raises the returned value; the caller catches it and
    returns the handler value through the linked RISC-V image. -/

def fullSsaHandlerFfiCalleeBody : Prog (RiscV.Word 64) :=
  .dec "ffiResult" .one (.const (BitVec.ofNat 64 0))
    (.seq
      (.extCall "inc" (.const (BitVec.ofNat 64 3))
        (.const (BitVec.ofNat 64 0)) (.const (BitVec.ofNat 64 0))
        (.const (BitVec.ofNat 64 0)))
      (.raise "E" (.var .local "ffiResult")))

def fullSsaHandlerFfiDeclarations : List (Decl (RiscV.Word 64)) :=
  [.exnDecl "E" .one,
   .function
     { name := "ffiRaise", inline := false, exported := false, params := [],
       body := fullSsaHandlerFfiCalleeBody, returnShape := .one },
   .function
     { name := "main", inline := false, exported := true, params := [],
       body := .dec "exception" .one (.const (BitVec.ofNat 64 0))
         (.call (some (none, some ("E", "exception",
           .return (.var .local "exception")))) "ffiRaise" []),
       returnShape := .one }]

def fullSsaHandlerFfiLinked :
    Option (List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64))) :=
  compileFlapjackRiscVViaAllocatedStackWithFullSsaLinked .rv64i
    (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value) [("inc", 7)]
    fullSsaHandlerFfiRemoveConfig fullSsaHandlerFfiDeclarations

def fullSsaHandlerFfiLookupEntry (label : Nat)
    : List (Nat × RiscV.Word 64 × List (RiscV.Instruction 64)) →
      Option (RiscV.Word 64)
  | [] => none
  | (candidate, entry, _) :: sections =>
      if candidate == label then some entry
      else fullSsaHandlerFfiLookupEntry label sections

def fullSsaHandlerFfiHost : RiscV.WordFfiHost 64 :=
  fun service configuration _ _ _ state =>
    if service = 7 then
      some { (RiscV.writeRegister state 11 (configuration + 1)) with
        pc := state.pc + 4 }
    else none

def fullSsaHandlerFfiMachineResult : Option (List (RiscV.Word 64)) := do
  let sections ← fullSsaHandlerFfiLinked
  let entry ← fullSsaHandlerFfiLookupEntry 2 sections
  let image := sections.flatMap (fun (_, _, code) => code)
  let returnAddress := BitVec.ofNat 64 348
  RiscV.executeFunctionAtWithFfi fullSsaHandlerFfiHost 8000 0 entry returnAddress [] image [2] []
    (RiscV.writeRegister (RiscV.zeroState 64) 1 returnAddress)

def fullSsaHandlerFfiSourceFunctions :
    List (FunName × List VarName × Prog (RiscV.Word 64)) :=
  [("ffiRaise", [], fullSsaHandlerFfiCalleeBody)]

def fullSsaHandlerFfiSourceMain : Prog (RiscV.Word 64) :=
  .dec "exception" .one (.const (BitVec.ofNat 64 0))
    (.call (some (none, some ("E", "exception",
      .return (.var .local "exception")))) "ffiRaise" [])

def fullSsaHandlerFfiSourceHandler : PanFfiHandler (RiscV.Word 64) :=
  fun function configuration _ _ _ locals =>
    if function == "inc" then
      some (updatePanLocal locals "ffiResult" (configuration + 1))
    else none

def fullSsaHandlerFfiLoopContext : CompileContext (RiscV.Word 64) :=
  { vars := [], functions := [], exceptions := [("E", BitVec.ofNat 64 0)],
    maxVar := 0, bytesInWord := BitVec.ofNat 64 8 }

def fullSsaHandlerFfiLoopFunctions :
    List (Nat × List Nat × LoopProg (RiscV.Word 64)) :=
  pipelineLoopFunctions .rv64i 1
    (compileToCrepe fullSsaHandlerFfiLoopContext
      fullSsaHandlerFfiDeclarations)

def fullSsaHandlerFfiLoopState : LoopState (RiscV.Word 64) :=
  { locals := fun _ => none
    globals := fun _ => none
    memory := fun _ => none }

def fullSsaHandlerFfiLoopHandler :
    FunName → RiscV.Word 64 → RiscV.Word 64 → RiscV.Word 64 → RiscV.Word 64 →
      LoopState (RiscV.Word 64) → Option (LoopState (RiscV.Word 64)) :=
  fun function configuration _ _ _ state =>
    if function == "inc" then
      some { state with
        locals := updateLoopLocal state.locals 1 (configuration + 1) }
    else none

def fullSsaHandlerFfiLoopResult : Option (List (RiscV.Word 64)) := do
  let (_, main) ← lookupLoopFunction 2 fullSsaHandlerFfiLoopFunctions
  let result ← evalLoopProgWithCallsAndFfi fullSsaHandlerFfiLoopFunctions
    fullSsaHandlerFfiLoopHandler 100 fullSsaHandlerFfiLoopState main
  pure (loopResultValues result)

#guard fullSsaHandlerFfiLinked.isSome

theorem fullSsaHandlerFfi_source_execution :
    (evalPanProgWithCallsAndFfi fullSsaHandlerFfiSourceFunctions
      fullSsaHandlerFfiSourceHandler 40
      (fun _ => none) fullSsaHandlerFfiSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = some [BitVec.ofNat 64 4] := by
  decide +kernel

theorem fullSsaHandlerFfi_machine_execution :
    fullSsaHandlerFfiMachineResult = some [BitVec.ofNat 64 4] := by
  native_decide

theorem fullSsaHandlerFfi_loop_execution :
    fullSsaHandlerFfiLoopResult = some [BitVec.ofNat 64 4] := by
  native_decide

theorem fullSsaHandlerFfi_source_machine_simulation :
    (evalPanProgWithCallsAndFfi fullSsaHandlerFfiSourceFunctions
      fullSsaHandlerFfiSourceHandler 40
      (fun _ => none) fullSsaHandlerFfiSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = fullSsaHandlerFfiMachineResult := by
  calc
    _ = some [BitVec.ofNat 64 4] := fullSsaHandlerFfi_source_execution
    _ = _ := fullSsaHandlerFfi_machine_execution.symm

theorem fullSsaHandlerFfi_source_loop_simulation :
    (evalPanProgWithCallsAndFfi fullSsaHandlerFfiSourceFunctions
      fullSsaHandlerFfiSourceHandler 40
      (fun _ => none) fullSsaHandlerFfiSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = fullSsaHandlerFfiLoopResult := by
  calc
    _ = some [BitVec.ofNat 64 4] := fullSsaHandlerFfi_source_execution
    _ = _ := fullSsaHandlerFfi_loop_execution.symm

/-! The same caught-handler/FFI program is also checked at the complete
    source-to-Crep boundary.  This closes the gap between the structured
    declaration-call proof and the later Loop/RISC-V regressions: the callee's
    FFI-produced result is raised, caught, and returned by the lowered Crep
    program. -/

def fullSsaHandlerFfiCrepState : CrepState (RiscV.Word 64) :=
  { locals := fun _ => none
    memory := fun _ => none }

def fullSsaHandlerFfiCrepHandler : CrepFfiHandler (RiscV.Word 64) :=
  fun function configuration _ _ _ state =>
    if function == "inc" then
      some (.returned { state with
        locals := updateCrepLocal state.locals 1 (configuration + 1) })
    else none

def fullSsaHandlerFfiCrepResult : Option (List (RiscV.Word 64)) :=
  evalCrepFullResult
    (compileToCrepe fullSsaHandlerFfiLoopContext
      fullSsaHandlerFfiDeclarations)
    (fun _ _ => none) fullSsaHandlerFfiCrepHandler
    defaultCrepSharedMemHandler 0 100 100 fullSsaHandlerFfiCrepState
    (compileProg fullSsaHandlerFfiLoopContext fullSsaHandlerFfiSourceMain)

theorem fullSsaHandlerFfi_source_crep_simulation :
    (evalPanProgWithCallsAndFfi fullSsaHandlerFfiSourceFunctions
      fullSsaHandlerFfiSourceHandler 40
      (fun _ => none) fullSsaHandlerFfiSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = fullSsaHandlerFfiCrepResult := by
  native_decide

theorem fullSsaHandlerFfi_source_crep_loop_machine_simulation :
    (evalPanProgWithCallsAndFfi fullSsaHandlerFfiSourceFunctions
      fullSsaHandlerFfiSourceHandler 40
      (fun _ => none) fullSsaHandlerFfiSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = fullSsaHandlerFfiCrepResult ∧
    (evalPanProgWithCallsAndFfi fullSsaHandlerFfiSourceFunctions
      fullSsaHandlerFfiSourceHandler 40
      (fun _ => none) fullSsaHandlerFfiSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = fullSsaHandlerFfiLoopResult ∧
    (evalPanProgWithCallsAndFfi fullSsaHandlerFfiSourceFunctions
      fullSsaHandlerFfiSourceHandler 40
      (fun _ => none) fullSsaHandlerFfiSourceMain).map (fun result =>
        match result with
        | .returned _ values => values
        | _ => []) = fullSsaHandlerFfiMachineResult := by
  exact ⟨fullSsaHandlerFfi_source_crep_simulation,
    fullSsaHandlerFfi_source_loop_simulation,
    fullSsaHandlerFfi_source_machine_simulation⟩

end Flapjack
