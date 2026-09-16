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

/-! Keep the complete Word-to-Word pass chain visible in diagnostics.  The
    source probe already exposes the front-end and selected program; these
    labels make a final-byte discrepancy attributable to SSA, a cleanup pass,
    or the allocator without requiring a second ad-hoc executable. -/
def dumpSourceWordPasses (entry : Nat × Nat × WordProg (RiscV.Word 64)) : IO Unit := do
  let (label, arity, body) := entry
  let flattened := RiscV.wordFlattenProgramFrom body
  let constFp := RiscV.wordConstFp flattened
  let fused := RiscV.wordFuseConditionsAndFold constFp
  let selected := RiscV.wordInstSelectProgramFrom fused
  let (_ssaState, renamedParameters, ssaProgram) :=
    wordFullSsaCcTrans arity selected
  let deadAfterSsa := RiscV.wordRemoveDeadProgram ssaProgram
  let cse := RiscV.wordCseProp deadAfterSsa
  let copy := RiscV.wordCopyProp cse
  let two := RiscV.wordThreeToTwoReg copy
  let unreach := RiscV.wordRemoveUnreachableAfterCopy two
  let dead := RiscV.wordRemoveDeadProgram unreach
  emit "stage=source_word_flattened" flattened
  emit "stage=source_word_const_fp" constFp
  emit "stage=source_word_fused" fused
  emit "stage=source_word_selected_passes" (label, arity, selected)
  emit "stage=source_word_ssa" (label, arity, renamedParameters, ssaProgram)
  emit "stage=source_word_dead_ssa" deadAfterSsa
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
  let spta := fun name =>
    (lookupNatInfo name bij.toAllocator).getD 0
  let moves0 := moves.map (RiscV.CakeRegAlloc.cakeUpdateMove spta)
  let movesF := RiscV.CakeRegAlloc.filterReversed
    (fun move => RiscV.CakeRegAlloc.cakeFullConsistencyOk state0 k
      move.2.1 move.2.2) moves0
  let scost := spillCosts.map (fun costs =>
    RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap bij.nextNode
      (costs.filterMap (fun entry =>
        (lookupNatInfo entry.1 bij.toAllocator).map
          (fun node => (node, entry.2)))))
  emit "stage=source_word_heuristics" (moves, spillCosts)
  emit "stage=source_word_allocator_inputs"
    (tree, forced, RiscV.CakeRegAlloc.cakeGetStackOnly dead, bij)
  let (allocationFuel, state1) :=
    RiscV.CakeRegAlloc.cakeInitAlloc1Heu movesF k state0
  let state2 := RiscV.CakeRegAlloc.cakeRptDoStep scost k allocationFuel state1
  let moveTable := RiscV.CakeRegAlloc.cakeMovesToSp moves0 []
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
  emit "stage=source_word_colour"
    (RiscV.CakeRegAlloc.cakeDoRegAlloc .irc scost
      RiscV.CakeRegAlloc.cakeRiscVRegisterCount moves tree forced
      (RiscV.CakeRegAlloc.cakeGetStackOnly dead))
  match RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead label
      (wordSsaAbiParameters arity) selected with
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
  | .ok (functions, _) => emit "stage=source_word_allocated" functions

def dumpSource (source : String) : IO UInt32 := do
  match Parser.parseTopDecs (BitVec.ofInt 64) source with
  | .error errors =>
      emit "stage=parse_error" errors
      return 1
  | .ok declarations =>
      emit "stage=parsed" declarations
      let checked := staticCheck declarations
      emit "stage=static_check" checked
      match compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
          (fun value => BitVec.ofNat 64 value) "main" declarations with
      | none =>
          IO.println "stage=compile_entry=none"
          return 1
      | some pipeline =>
          dumpPipeline pipeline
          return 0

def usage : String :=
  "Usage: lake exe flapjack-debug [SOURCE.pnk]\n" ++
  "Read Pancake source from SOURCE.pnk or stdin and print intermediate stages."

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [] =>
      let stdin ← IO.getStdin
      dumpSource (← stdin.readToEnd)
  | ["--help"] | ["-h"] =>
      IO.println usage
      return 0
  | [path] =>
      dumpSource (← IO.FS.readFile path)
  | _ =>
      IO.eprintln usage
      return 2

end Flapjack.Debug

def main (arguments : List String) : IO UInt32 := Flapjack.Debug.main arguments
