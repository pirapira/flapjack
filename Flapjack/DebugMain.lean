import Flapjack.RiscV.PipelineDiagnostics

/-!
# Intermediate pipeline dump

This executable is intentionally diagnostic rather than a second compiler
entry point.  It prints the values returned by the source pipeline at the
same boundaries that are named in CakeML's `pan_passes` development.  The
output is designed to be saved beside a differential-fuzz finding and
compared with `scripts/pancake-stage-probe.sml`.
-/

namespace Flapjack.Debug

open Flapjack Flapjack.RiscV

def emit [Repr α] (label : String) (value : α) : IO Unit :=
  IO.println (label ++ "=" ++ repr value)

/-! A compact view of the source-shaped linked Lab program.  The ordinary
    pipeline dump renders complete StackProg bodies, which is useful for
    pass-by-pass comparisons but too large for a relocation discrepancy in a
    large guest.  This view keeps only line constructors, stored lengths, and
    byte positions for one section. -/

def labLineSummary : LabLine (RiscV.Word 64) → String
  | .label _ label length => s!"label {label} length={length}"
  | .asm operation _ length => s!"asm {repr operation} length={length}"
  | .labAsm operation _ length => s!"labAsm {repr operation} length={length}"

def dumpLabSectionLines (stage : String) (target low high : Nat)
    (sectionData : LabSection (RiscV.Word 64)) : IO Unit := do
  IO.println
    (s!"lab-stage={stage} section={sectionData.name} lines={sectionData.lines.length} " ++
      s!"stored-bytes={RiscV.labStoredSectionLength sectionData.lines}")
  let rec loop (position index : Nat) : List (LabLine (RiscV.Word 64)) → IO Unit
    | [] => pure ()
    | line :: lines => do
        let length := RiscV.labStoredLineLength line
        let next := position + length
        if position <= high && next >= low then
          IO.println
            (s!"lab-line section={target} index={index} position={position} " ++
              labLineSummary line)
        loop next (index + 1) lines
  loop 1000 0 sectionData.lines

def dumpLabSection (stage : String) (target low high : Nat)
    (program : LabProgram (RiscV.Word 64)) : IO Unit :=
  match program.find? (fun sectionData => sectionData.name == target) with
  | some sectionData => dumpLabSectionLines stage target low high sectionData
  | none => IO.println s!"lab-stage={stage} missing-section={target}"

def sourceRuntimeLabProgram
    (initialLabel : Nat)
    (functions : List (Nat × List Nat × StackProg Nat)) :
    LabProgram (RiscV.Word 64) :=
  let removeConfig : StackRemoveConfig :=
    { storeBase := 10
      currHeap := 12
      scratch := 31
      addressScratch := 29
      stackPointer := 24
      bytesInWord := 8
      stackBase := 25
      wordShift := 3 }
  let removeConfig := RiscV.cakeStackRemoveConfig removeConfig
  let programs :=
    (stackRaiseStubLocation,
        stackRaiseStub false removeConfig.addressScratch) ::
      stackAllocCompileWithSimpleGcAndStoreConsts
        { gcStubLocation := stackGcStubLocation, returnLabel := 0,
          firstFreshLabel := stackFunctionFirstLabel }
        {} stackStoreConstsStubLocation RiscV.CakeRegAlloc.cakeRiscVRegisterCount
        (functions.map (fun (label, _, body) => (label, body)))
  match stackProgramsWithLongDivRuntime removeConfig programs with
  | none => []
  | some programs =>
      let programs := stackRawCallPrograms programs
      (programs.map (fun (sectionId, program) =>
        if sectionId = cakeLongDiv1Location || sectionId = cakeLongDivLocation then
          labProgramToEntrySection sectionId 0 0
            (stackMapRegisters riscvRegisterName
              (stackRemoveComplete removeConfig program))
        else
          labProgramToEntrySection sectionId 0 initialLabel
            (stackMapRegisters riscvRegisterName
              (stackRemoveComplete removeConfig program)))).map labSectionNatToWord

def dumpLinkedLab (pipeline : FlapjackPipelineResult (RiscV.Word 64))
    (target low high : Nat) : IO Unit := do
  let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel
    pipeline.crepe
  let sourceWord := panToWordCompileProg sourceLoop
  match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
      (RiscV.wordStackInitialBitmaps false) sourceWord with
  | .error error => emit "stage=lab_dump_error" error
  | .ok (functions, _) =>
      let program := sourceRuntimeLabProgram
        (fullSsaInitialLabLabel functions) functions
      let sourceProgram := program.filter (fun sectionData => sectionData.name >= 3)
      let initial := RiscV.labInitialStoredProgram sourceProgram
      let initialHaltPc := RiscV.pancakeInitialSourceBase +
        RiscV.labStoredProgramLength initial
      let encoded := RiscV.labEncodeStoredProgramStable 8 { services := [] }
        RiscV.pancakeInitialSourceBase 1000 initialHaltPc initial
      let relabelled := RiscV.labUpdateStoredLabelLengths 1000 encoded
      let haltPc := 1000 + RiscV.labStoredProgramLength relabelled
      let labels := RiscV.labLabelIndexOf
        (RiscV.labCollectPancakeRuntimeStoredLabels relabelled)
      let final := RiscV.labEncodeStoredProgram { services := [] } labels
        1000 1000 haltPc relabelled
      dumpLabSection "initial" target low high initial
      dumpLabSection "encoded" target low high encoded
      dumpLabSection "relabelled" target low high relabelled
      dumpLabSection "final" target low high final

def clashTreeSets : WordClashTree → List (List Nat)
  | .delta _ _ => []
  | .set names => [names]
  | .branch live thenBranch elseBranch =>
      (live.toList ++ clashTreeSets thenBranch ++ clashTreeSets elseBranch)
  | .seq first second => clashTreeSets first ++ clashTreeSets second

/-! Keep the complete Word-to-Word pass chain visible in diagnostics.  The
    source probe already exposes the front-end and selected program; these
    labels make a final-byte discrepancy attributable to SSA, a cleanup pass,
    or the allocator without requiring a second ad-hoc executable. -/
def dumpSourceWordPasses (entry : Nat × Nat × WordProg (RiscV.Word 64)) : IO Unit := do
  let (label, arity, body) := entry
  let flattened := RiscV.wordFlattenProgramFrom body
  let constFp := RiscV.wordConstFp flattened
  let duplicate := RiscV.wordSimpDuplicateIf constFp
  let fused := RiscV.wordFuseConditionsAndFold constFp
  let selected := RiscV.wordInstSelectProgramFrom fused
  /- Keep these labels for probe compatibility, but do not run the legacy
     front-end DCE/unreachable helper here.  Cake keeps these tails through
     full SSA; `word_unreach` runs later, after cleanup and allocation. -/
  let dce := selected
  let unallocated := selected
  let (_ssaState, renamedParameters, ssaProgram) :=
    wordFullSsaCcTrans arity unallocated
  let (deadAfterSsa, deadLive, deadNLive) :=
    RiscV.wordDeadCodeWithStores ssaProgram [] []
      (RiscV.wordDeadReturnLabels ssaProgram) []
  let cse := RiscV.wordCseProp deadAfterSsa
  let copy := RiscV.wordCopyProp cse
  let two := RiscV.wordThreeToTwoReg copy
  let unreach := RiscV.wordRemoveUnreachableAfterCopy two
  let dead := RiscV.wordRemoveDeadProgram unreach
  emit "stage=source_word_flattened" flattened
  emit "stage=source_word_const_fp" constFp
  emit "stage=source_word_duplicate" duplicate
  emit "stage=source_word_fused" fused
  emit "stage=source_word_selected_passes" (label, arity, selected)
  emit "stage=source_word_dce" dce
  emit "stage=source_word_unallocated" unallocated
  emit "stage=source_word_ssa" (label, arity, renamedParameters, ssaProgram)
  emit "stage=source_word_dead_ssa" deadAfterSsa
  emit "stage=source_word_dead_ssa_live" (deadLive, deadNLive)
  emit "stage=source_word_cse" cse
  emit "stage=source_word_copy" copy
  emit "stage=source_word_two_reg" two
  emit "stage=source_word_unreach" unreach
  emit "stage=source_word_dead" dead
  let tree := wordClashTree dead []
  let forced := RiscV.CakeRegAlloc.cakeGetForced dead
  let (wordMoves, spillCosts) := wordGetHeuristics 3 label dead
  let moves := wordMoves.map (fun move => (move.priority, (move.left, move.right)))
  let bij := RiscV.CakeRegAlloc.cakeMkBij tree
  let k := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
  let state0 := RiscV.CakeRegAlloc.cakeInitRaState tree forced
    (RiscV.CakeRegAlloc.cakeGetStackOnly dead)
  let spta := RiscV.CakeAlloc.spDefault bij.toAllocator
  let moves0 := moves.map (RiscV.CakeRegAlloc.cakeUpdateMove spta)
  let movesF := RiscV.CakeRegAlloc.filterReversed
    (fun move => RiscV.CakeRegAlloc.cakeFullConsistencyOk state0 k
      move.2.1 move.2.2) moves0
  let scost := spillCosts.map
    (RiscV.CakeRegAlloc.cakeSpillCostMap bij.nextNode)
  emit "stage=source_word_heuristics" (moves, spillCosts)
  emit "stage=source_word_allocator_inputs"
    (tree, forced, RiscV.CakeRegAlloc.cakeGetStackOnly dead, bij)
  emit "stage=source_word_allocator_sets" (clashTreeSets tree)
  let (allocationFuel, state1) :=
    RiscV.CakeRegAlloc.cakeInitAlloc1Heu movesF k state0
  let state2 := RiscV.CakeRegAlloc.cakeRptDoStep scost k allocationFuel state1
  let moveTable := RiscV.CakeRegAlloc.cakeMovesToSp moves0
    (RiscV.CakeRegAlloc.CakeNodeMap.ofSize bij.nextNode)
  let state3 := RiscV.CakeRegAlloc.cakeAssignAtemps k state2.stack
    (fun state node colours =>
      RiscV.CakeRegAlloc.cakeBiasedPref state
        (RiscV.CakeRegAlloc.cakeResortMovesSp moveTable) node colours) state2
  let state4 := RiscV.CakeRegAlloc.cakeAssignStemps k
    (fun state node bads =>
      RiscV.CakeRegAlloc.cakeNegBiasedPref state k
        (RiscV.CakeRegAlloc.cakeResortMovesSp moveTable) node bads) state3
  emit "stage=source_word_allocator_trace"
    (allocationFuel, state1.simpWl, state1.freezeWl, state1.spillWl,
      state2.stack, state2.coalesced, state3.nodeTag, state4.nodeTag)
  let colouring := RiscV.CakeRegAlloc.cakeDoRegAlloc .irc scost
    RiscV.CakeRegAlloc.cakeRiscVRegisterCount moves tree forced
    (RiscV.CakeRegAlloc.cakeGetStackOnly dead)
  emit "stage=source_word_colour" colouring
  emit "stage=source_word_total_colour"
    (colouring.map (fun colouring =>
      let colour := RiscV.CakeAlloc.totalColour colouring
      [ (0, colour 0), (2, colour 2), (4, colour 4), (21, colour 21),
        (25, colour 25), (37, colour 37), (41, colour 41),
        (47, colour 47), (51, colour 51), (73, colour 73),
        (197, colour 197), (201, colour 201) ]))
  match RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead label
      (wordSsaAbiParameters arity) unallocated with
  | none => emit "stage=source_word_allocator" "none"
  | some (_, parameters, program, allocation) =>
      emit "stage=source_word_allocator" (parameters, program, allocation)

def dumpPipeline (pipeline : FlapjackPipelineResult (RiscV.Word 64)) : IO Unit := do
  emit "stage=simplified" pipeline.simplified
  emit "stage=structured" pipeline.structured
  emit "stage=global_initializers" pipeline.globals.initializers
  emit "stage=global_declarations" pipeline.globals.declarations
  emit "stage=crepe" pipeline.crepe
  emit "stage=loop" pipeline.loop
  emit "stage=word" pipeline.word
  let selected := pipeline.word.map (fun (label, parameters, body) =>
    (label, parameters, RiscV.wordInstSelectProgramFrom body))
  emit "stage=word_inst_select" selected
  /- The runtime-image CLI follows the source-shaped `pan_to_word` path below,
     rather than the historical `pipeline.word` helper above.  Dump its
     boundaries too so source-to-RISC-V discrepancies can be localized against
     Cake's `loop_to_word` probe. -/
  let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel
    pipeline.crepe
  let sourceWord := panToWordCompileProg sourceLoop
  emit "stage=source_loop" sourceLoop
  emit "stage=source_word" sourceWord
  for entry in sourceWord do
    dumpSourceWordPasses entry
  let sourceSelected := sourceWord.map (fun (label, arity, body) =>
    (label, arity,
      RiscV.wordInstSelectProgramFrom
        (RiscV.wordFuseConditionsAndFold
          (RiscV.wordConstFp (RiscV.wordFlattenProgramFrom body)))))
  emit "stage=source_word_inst_select" sourceSelected
  match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
      (RiscV.wordStackInitialBitmaps false) sourceWord with
  | .error error => emit "stage=source_word_allocated_error" error
  | .ok (functions, _) =>
      emit "stage=source_word_allocated" functions
      /- The source-facing compiler enters the Cake-shaped stack-removal
         path after this boundary.  Keep the post-removal form in the probe
         as well: a final byte mismatch that is absent here belongs to Lab or
         target encoding, while one already present here belongs to the
         allocator/StackRemove boundary. -/
      let removeConfig : StackRemoveConfig :=
        { storeBase := 10
          currHeap := 12
          scratch := 31
          addressScratch := 29
          stackPointer := 24
          bytesInWord := 8
          stackBase := 25
          wordShift := 3 }
      let removed := functions.map (fun (label, parameters, body) =>
        (label, parameters,
          stackMapRegisters RiscV.riscvRegisterName
            (stackRemoveComplete (RiscV.cakeStackRemoveConfig removeConfig) body)))
      emit "stage=source_stack_removed" removed

/-! The complete dump is intentionally expensive on a large guest because it
    renders every function at every boundary.  A label-filtered dump keeps the
    same pass sequence for one function, which makes the first divergent
    allocator state inspectable without forcing the whole diagnostic output. -/
def dumpPipelineTarget (pipeline : FlapjackPipelineResult (RiscV.Word 64))
    (target : Nat) : IO Unit := do
  let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel
    pipeline.crepe
  let sourceWord := panToWordCompileProg sourceLoop
  match sourceLoop.find? (fun entry => entry.1 == target) with
  | some loopEntry => emit "stage=target_loop" loopEntry
  | none => emit "stage=target_loop_not_found" target
  match pipeline.crepe.zip sourceWord |>.find?
      (fun pair => pair.2.1 == target) with
  | none => emit "stage=target_not_found" target
  | some (function, entry) =>
      emit "stage=target" (target, function.name, function.params, entry.2)
      dumpSourceWordPasses entry
      match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
          (RiscV.wordStackInitialBitmaps false) [entry] with
      | .error error => emit "stage=target_allocated_error" error
      | .ok ([(label, parameters, body)], bitmaps) =>
          emit "stage=target_allocated" (label, parameters, body, bitmaps)
      | .ok (functions, bitmaps) =>
          emit "stage=target_allocated_unexpected" (functions, bitmaps)

/-! Resolve a target by its source-level function name.  Labels are convenient
    for generated helpers, but names are much more useful when comparing a
    minimized witness with Cake's source-level stage probe. -/
def dumpPipelineNamed (pipeline : FlapjackPipelineResult (RiscV.Word 64))
    (targetName : String) : IO Unit := do
  let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel
    pipeline.crepe
  let sourceWord := panToWordCompileProg sourceLoop
  match pipeline.crepe.zip sourceWord |>.find?
      (fun pair => pair.1.name == targetName) with
  | none => emit "stage=target_name_not_found" targetName
  | some (_, entry) => dumpPipelineTarget pipeline entry.1

def dumpSource (source : String) (target : Option Nat := none)
    (targetName : Option String := none) : IO UInt32 := do
  match hparse : Parser.parseTopDecs (BitVec.ofInt 64) source with
  | .error errors =>
      emit "stage=parse_error" errors
      return 1
  | .ok declarations =>
      emit "stage=parsed" declarations
      let checked := staticCheck declarations
      emit "stage=static_check" checked
      let parsedByteRanged := Parser.parseTopDecs_declByteRanged
        (BitVec.ofInt 64) source false declarations hparse
      let targetByteRanged := panTargetDeclarationsWithDefaultMain_byteRanged
        declarations parsedByteRanged
      /- Minimized differential witnesses often have no `main`: the reducer is
         allowed to remove declarations that are irrelevant to the selected
         runtime section.  Use the target-facing entry point here, just as the
         artifact compiler does, so those witnesses still get a complete
         diagnostic dump with Pancake's synthetic `main = return 0` fallback. -/
      let some pipeline := compileFlapjackEntryCake .rv64i (BitVec.ofNat 64 8)
        (fun value => BitVec.ofNat 64 value) "main"
        (panTargetDeclarationsWithDefaultMain declarations)
        (some (.isTrue targetByteRanged))
        | emit "stage=entry_error" ("main not found" : String)
          return 1
      match target, targetName with
      | some target, _ => dumpPipelineTarget pipeline target
      | none, some targetName => dumpPipelineNamed pipeline targetName
      | none, none => dumpPipeline pipeline
      return 0

def dumpLabSource (source : String) (target : Nat) : IO UInt32 := do
  match hparse : Parser.parseTopDecs (BitVec.ofInt 64) source with
  | .error errors =>
      emit "stage=parse_error" errors
      return 1
  | .ok declarations =>
      let parsedByteRanged := Parser.parseTopDecs_declByteRanged
        (BitVec.ofInt 64) source false declarations hparse
      let targetByteRanged := panTargetDeclarationsWithDefaultMain_byteRanged
        declarations parsedByteRanged
      let some pipeline := compileFlapjackEntryCake .rv64i (BitVec.ofNat 64 8)
        (fun value => BitVec.ofNat 64 value) "main"
        (panTargetDeclarationsWithDefaultMain declarations)
        (some (.isTrue targetByteRanged))
        | emit "stage=entry_error" ("main not found" : String)
          return 1
      dumpLinkedLab pipeline target 0 (Nat.succ 1000000000)
      return 0

def usage : String :=
  "Usage: lake exe flapjack-debug [SOURCE.pnk]\n" ++
  "       lake exe flapjack-debug --label LABEL [SOURCE.pnk]\n" ++
  "       lake exe flapjack-debug --function NAME [SOURCE.pnk]\n" ++
  "       lake exe flapjack-debug --lab-label LABEL [SOURCE.pnk]\n" ++
  "Read Pancake source from SOURCE.pnk or stdin and print intermediate stages.\n" ++
  "With --label or --function, render only the selected source Word function.\n" ++
  "With --lab-label, render compact linked-Lab lines for one section."

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [] =>
      let stdin ← IO.getStdin
      dumpSource (← stdin.readToEnd)
  | ["--help"] | ["-h"] =>
      IO.println usage
      return 0
  | ["--label", rawLabel] =>
      match rawLabel.toNat? with
      | none =>
          IO.eprintln ("invalid numeric label: " ++ rawLabel)
          return 2
      | some label =>
          let stdin ← IO.getStdin
          dumpSource (← stdin.readToEnd) (some label)
  | ["--label", rawLabel, path] =>
      match rawLabel.toNat? with
      | none =>
          IO.eprintln ("invalid numeric label: " ++ rawLabel)
          return 2
      | some label =>
          dumpSource (← IO.FS.readFile path) (some label)
  | ["--function", name] =>
      let stdin ← IO.getStdin
      dumpSource (← stdin.readToEnd) none (some name)
  | ["--function", name, path] =>
      dumpSource (← IO.FS.readFile path) none (some name)
  | ["--lab-label", rawLabel] =>
      match rawLabel.toNat? with
      | none =>
          IO.eprintln ("invalid numeric label: " ++ rawLabel)
          return 2
      | some label =>
          let stdin ← IO.getStdin
          dumpLabSource (← stdin.readToEnd) label
  | ["--lab-label", rawLabel, path] =>
      match rawLabel.toNat? with
      | none =>
          IO.eprintln ("invalid numeric label: " ++ rawLabel)
          return 2
      | some label =>
          dumpLabSource (← IO.FS.readFile path) label
  | [path] =>
      dumpSource (← IO.FS.readFile path)
  | _ =>
      IO.eprintln usage
      return 2

end Flapjack.Debug

def main (arguments : List String) : IO UInt32 := Flapjack.Debug.main arguments
