import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.RiscV.ArtifactFormat


/-!
# Front-end stage timing driver

Untracked performance driver.  `Flapjack/PerfMain.lean`-style subphase timing
exists for the Word/allocator backend; this one measures the *whole-program*
distribution across the source pipeline stages so a super-linear stage can be
identified from the stage totals alone.

Each stage is forced with a cheap structural size so that Lean's lazy `let`
bindings cannot shift a stage's cost into the next measurement.

Environment:
* `PERF_INPUT`  — Pancake source file (required)
* `PERF_ENTRY`  — entry function name (default `main`)
-/

namespace Flapjack.PerfFront

open Flapjack Flapjack.Parser

/-- Mirrors `Flapjack.compileRemoveConfig` in `Flapjack/CompileMain.lean`; kept
    local so this driver does not import the compiler entry point. -/
def perfRemoveConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 24
    bytesInWord := 8
    stackBase := 25
    wordShift := 3
    jump := false }

/-- Structural node count of a `LoopProg`, used only to force evaluation. -/
partial def countLoop (program : LoopProg α) : Nat :=
  match program with
  | .seq first second => 1 + countLoop first + countLoop second
  | .ite _ _ _ thenBranch elseBranch _ => 1 + countLoop thenBranch + countLoop elseBranch
  | .loop _ body _ => 1 + countLoop body
  | .mark body => 1 + countLoop body
  | _ => 1

/-- Structural node count of a `WordProg`, used only to force evaluation. -/
partial def countWord (program : WordProg α) : Nat :=
  match program with
  | .seq first second => 1 + countWord first + countWord second
  | .ite _ _ _ thenBranch elseBranch => 1 + countWord thenBranch + countWord elseBranch
  | .loop _ body _ => 1 + countWord body
  | .mustTerminate body => 1 + countWord body
  | _ => 1

/-- Structural node count of a source `Prog`, used only to force evaluation. -/
partial def countProg (program : Prog α) : Nat :=
  match program with
  | .dec _ _ _ body => 1 + countProg body
  | .seq first second => 1 + countProg first + countProg second
  | .ite _ thenBranch elseBranch => 1 + countProg thenBranch + countProg elseBranch
  | .while _ body => 1 + countProg body
  | .decCall _ _ _ _ body => 1 + countProg body
  | .call info _ _ =>
      1 + match info with
          | some (_, some (_, _, handler)) => countProg handler
          | _ => 0
  | _ => 1

def countDecl (declaration : Decl α) : Nat :=
  match declaration with
  | .function function => 1 + countProg function.body
  | _ => 1

def countDecls (declarations : List (Decl α)) : Nat :=
  declarations.foldl (fun acc declaration => acc + countDecl declaration) 0

/-- Structural node count of a `CrepProg`, used only to force evaluation. -/
partial def countCrep (program : CrepProg α) : Nat :=
  match program with
  | .dec _ _ body => 1 + countCrep body
  | .seq first second => 1 + countCrep first + countCrep second
  | .ite _ thenBranch elseBranch => 1 + countCrep thenBranch + countCrep elseBranch
  | .while _ body => 1 + countCrep body
  | .call returnInfo _ _ =>
      1 + match returnInfo with
          | some (_, some (_, handler)) => countCrep handler
          | _ => 0
  | _ => 1

def countCrepFunctions (functions : List (CompiledFunction α)) : Nat :=
  functions.foldl (fun acc function => acc + countCrep function.body) 0

def stage (name : String) (start : Nat) (size : Nat) : IO Nat := do
  let now ← IO.monoMsNow
  IO.println s!"PERF stage {name} {now - start} ms size={size}"
  (← IO.getStdout).flush
  return now

/-- Per-function backend (stage 5) timing: allocator + word-to-stack for one
    function at a time, so the whole-program cost distribution is visible. -/
partial def backendWalk
    (entries : List (Nat × List Nat × LoopProg (RiscV.Word 64))) (index : Nat) :
    IO Unit := do
  match entries with
  | [] => IO.println "PERF backend done"
  | entry :: rest => do
      let start ← IO.monoMsNow
      let outcome := pipelineWordFunctionsAllocatedWithSpillsAndFullSsaChecked [entry]
      let status := match outcome with
        | .ok result => s!"ok n={result.length}"
        | .error _ => "FAILED"
      let now ← IO.monoMsNow
      IO.println s!"PERF backend fn[{index}] label={entry.1} {now - start} ms {status}"
      (← IO.getStdout).flush
      backendWalk rest (index + 1)

/-- Compare the frame-slot count the pipeline actually uses (a second full
    allocation of the unflattened body, `cakeWordStackVarCount`) against the
    one CakeML's `compile_prog` would use: `stack_var_count` of the program
    that word-to-stack is actually lowering, which the allocator has already
    computed and returned as `allocation.nextSpill`. -/
partial def frameWalk
    (entries : List (Nat × Nat × WordProg (RiscV.Word 64))) (index : Nat) :
    IO Unit := do
  match entries with
  | [] => IO.println "PERF frame done"
  | (label, arity, body) :: rest => do
      let wordParameters := wordSsaAbiParameters arity
      let unflattenedBody := wordProgDCE (RiscV.wordFuseConditions body)
      let unallocatedBody := RiscV.wordRemoveUnreachable (wordProgDCE
        (RiscV.wordInstSelectProgramFrom
          (RiscV.wordFuseConditionsAndFold
            (RiscV.wordConstFp
              (RiscV.wordFlattenProgramFrom body)))))
      match RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead
          label wordParameters unallocatedBody with
      | none => IO.println s!"PERF frame fn[{index}] label={label} ALLOC-FAILED"
      | some (_, _, renamedProgram, allocation) => do
          let bitmapSites := RiscV.wordProgHasBitmapSites renamedProgram
          let current :=
            if bitmapSites then
              RiscV.CakeRegAlloc.cakeWordStackVarCount label wordParameters
                RiscV.CakeRegAlloc.cakeRiscVRegisterCount unflattenedBody
            else 0
          let cake := allocation.nextSpill
          let other := max (wordParameters.length - 12)
            (RiscV.wordProgMaxCallArguments renamedProgram - 12)
          let maxSlot := allocation.locations.foldl
            (fun acc entry =>
              match entry.2 with
              | .stack slot => max acc slot
              | _ => acc) 0
          let usesStack := allocation.locations.any (fun entry =>
            match entry.2 with | .stack _ => true | _ => false)
          let finalCurrent := max current other
          let frameCurrent := if finalCurrent = 0 then 0 else finalCurrent + 1
          let inFrame := !usesStack || maxSlot < frameCurrent
          IO.println s!"PERF frame fn[{index}] label={label} bitmapSites={bitmapSites} current={current} cakeNextSpill={cake} other={other} finalCurrent={finalCurrent} finalCake={max cake other} agree={finalCurrent == max cake other} maxSlot={maxSlot} usesStack={usesStack} frameCurrent={frameCurrent} inFrame={inFrame}"
          (← IO.getStdout).flush
      frameWalk rest (index + 1)

/-- Per-function timing of the runtime-image back end, the one
    `flapjack-compile --assembly` runs. -/
partial def imageWalk
    (entries : List (Nat × Nat × WordProg (RiscV.Word 64))) (index : Nat) :
    IO Unit := do
  match entries with
  | [] => IO.println "PERF image done"
  | entry :: rest => do
      let start ← IO.monoMsNow
      let outcome := pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
        (RiscV.wordStackInitialBitmaps false) [entry]
      let status := match outcome with
        | .ok (functions, _) => s!"ok n={functions.length}"
        | .error error => s!"ERROR {repr error}"
      let now ← IO.monoMsNow
      IO.println s!"PERF imagefn[{index}] label={entry.1} {now - start} ms {status}"
      (← IO.getStdout).flush
      imageWalk rest (index + 1)

/-- `cakeRptDoStep` with each `do_step` phase timed and counted. -/
partial def timedRpt (scost : Option (RiscV.CakeRegAlloc.CakeNodeMap Nat)) (k : Nat) :
    Nat → RiscV.CakeRegAlloc.CakeRaState →
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    IO RiscV.CakeRegAlloc.CakeRaState
  | 0, state, tsi, tco, tpf, tfr, tsp, nsi, nco, npf, nfr, nsp => do
      IO.println s!"PERF steps simplify {tsi} ms n={nsi} | coalesce {tco} ms n={nco} | prefreeze {tpf} ms n={npf} | freeze {tfr} ms n={nfr} | spill {tsp} ms n={nsp}"
      (← IO.getStdout).flush
      pure state
  | fuel + 1, state, tsi, tco, tpf, tfr, tsp, nsi, nco, npf, nfr, nsp => do
      let t0 ← IO.monoMsNow
      let (b1, s1) := RiscV.CakeRegAlloc.cakeDoSimplify k state
      let t1 ← IO.monoMsNow
      if b1 then
        timedRpt scost k fuel s1 (tsi + (t1 - t0)) tco tpf tfr tsp (nsi+1) nco npf nfr nsp
      else
        let (b2, s2) := RiscV.CakeRegAlloc.cakeDoCoalesce k state
        let t2 ← IO.monoMsNow
        if b2 then
          timedRpt scost k fuel s2 (tsi + (t1 - t0)) (tco + (t2 - t1)) tpf tfr tsp nsi (nco+1) npf nfr nsp
        else
          -- split prefreeze: its own body versus the do_simplify it ends with
          let pf0 ← IO.monoMsNow
          let fwl := RiscV.CakeRegAlloc.filterReversed
            (fun x => RiscV.CakeRegAlloc.cakeIsNotCoalesced state x) state.freezeWl
          let stateA := { state with
            spillWl := RiscV.CakeRegAlloc.filterReversed
              (fun x => RiscV.CakeRegAlloc.cakeIsNotCoalesced state x) state.spillWl }
          let uam := RiscV.CakeRegAlloc.filterReversed
            (fun m => RiscV.CakeRegAlloc.cakeConsistencyOk stateA m.2.1 m.2.2)
            stateA.unavailMovesWl
          let pf1 ← IO.monoMsNow
          let stateB := RiscV.CakeRegAlloc.cakeResetMoveRelated uam stateA
          let pf2 ← IO.monoMsNow
          let stateC := { stateB with unavailMovesWl := uam }
          let (freeze, simp) := RiscV.CakeRegAlloc.partitionReversed
            (fun v => RiscV.CakeRegAlloc.cakeMoveRelatedSub stateC v) fwl
          let stateD := RiscV.CakeRegAlloc.cakeAddSimpWl simp stateC
          let stateE := { stateD with freezeWl := freeze }
          let pf3 ← IO.monoMsNow
          let (_, _) := RiscV.CakeRegAlloc.cakeDoSimplify k stateE
          let pf4 ← IO.monoMsNow
          IO.println s!"PERF prefreeze filters {pf1 - pf0} | resetMoveRelated {pf2 - pf1} | partition {pf3 - pf2} | doSimplify {pf4 - pf3} | fwl={fwl.length} uam={uam.length} spill={stateA.spillWl.length} simp={simp.length}"
          (← IO.getStdout).flush
          let (b3, s3) := RiscV.CakeRegAlloc.cakeDoPrefreeze k state
          let t3 ← IO.monoMsNow
          if b3 then
            timedRpt scost k fuel s3 (tsi + (t1 - t0)) (tco + (t2 - t1)) (tpf + (t3 - t2)) tfr tsp nsi nco (npf+1) nfr nsp
          else
            let (b4, s4) := RiscV.CakeRegAlloc.cakeDoFreeze k state
            let t4 ← IO.monoMsNow
            if b4 then
              timedRpt scost k fuel s4 (tsi + (t1 - t0)) (tco + (t2 - t1)) (tpf + (t3 - t2)) (tfr + (t4 - t3)) tsp nsi nco npf (nfr+1) nsp
            else
              let (b5, s5) := RiscV.CakeRegAlloc.cakeDoSpill scost k state
              let t5 ← IO.monoMsNow
              if b5 then
                timedRpt scost k fuel s5 (tsi + (t1 - t0)) (tco + (t2 - t1)) (tpf + (t3 - t2)) (tfr + (t4 - t3)) (tsp + (t5 - t4)) nsi nco npf nfr (nsp+1)
              else
                timedRpt scost k 0 s5 (tsi + (t1 - t0)) (tco + (t2 - t1)) (tpf + (t3 - t2)) (tfr + (t4 - t3)) (tsp + (t5 - t4)) nsi nco npf nfr nsp

/-- Smallest sub-program of a failing function that `wordToStackProgNat`
    still cannot lower, with the path that reaches it. -/
partial def findLowerFailure (config : RiscV.WordStackConfig) :
    List Nat → WordProg Nat → List Nat × WordProg Nat
  | path, program =>
      let children : List (Nat × WordProg Nat) :=
        match program with
        | .seq first second => [(0, first), (1, second)]
        | .ite _ _ _ thenBranch elseBranch => [(0, thenBranch), (1, elseBranch)]
        | .loop _ body _ => [(0, body)]
        | .mustTerminate body => [(0, body)]
        | .call (some (_, _, returnCode, _, _)) _ _ (some (_, handler, _, _)) =>
            [(0, returnCode), (1, handler)]
        | .call (some (_, _, returnCode, _, _)) _ _ none => [(0, returnCode)]
        | .call none _ _ (some (_, handler, _, _)) => [(1, handler)]
        | _ => []
      match children.find? (fun child =>
          (RiscV.wordToStackProgNat config child.2).isNone) with
      | some (index, child) => findLowerFailure config (path ++ [index]) child
      | none => (path, program)

/-- Force a `Nat` to weak head normal form so a stage timing measures the
    work of that stage rather than deferring it to the final print. -/
@[noinline] def force (value : Nat) : IO Nat := do
  if value == 0 then pure 0 else pure value

/-- Split `wordGetHeuristics` into its four observable stages across every
    function of a program, so the dominant term inside the heuristics phase is
    attributable. -/
partial def heurWalk
    (entries : List (Nat × Nat × WordProg (RiscV.Word 64))) (index : Nat)
    (tm tsc tcanon tcost chk : Nat) : IO Unit := do
  match entries with
  | [] =>
      IO.println s!"PERF heur prioritizedMoves {tm} | spillCostsFast {tsc} | canonicalizeMoves {tcanon} | coalesceMoveCost {tcost} | checksum {chk}"
  | (label, arity, body) :: rest => do
      let wordParameters := wordSsaAbiParameters arity
      let unallocatedBody := RiscV.wordRemoveUnreachable (wordProgDCE
        (RiscV.wordInstSelectProgramFrom
          (RiscV.wordFuseConditionsAndFold
            (RiscV.wordConstFp (RiscV.wordFlattenProgramFrom body)))))
      let (_, _, ssa0) := wordFullSsaCcTrans wordParameters.length unallocatedBody
      let ssaProgram := RiscV.wordRemoveDeadProgram (RiscV.wordRemoveUnreachableAfterCopy
        (RiscV.wordThreeToTwoReg (RiscV.wordCopyProp (RiscV.wordCseProp
          (RiscV.wordRemoveDeadProgram ssa0)))))
      let chk := chk + countWord ssaProgram
      let h0 ← IO.monoMsNow
      let moves := wordProgPrioritizedMoves ssaProgram
      let m0 := moves.foldl (fun acc m => acc + m.priority + m.left + m.right) 0
      let _ ← force m0
      let h1 ← IO.monoMsNow
      let spillCosts := wordHeuristicSpillCostsFast label ssaProgram
      let m1 := spillCosts.foldl (fun acc e => acc + e.1 + e.2) 0
      let _ ← force m1
      let h2 ← IO.monoMsNow
      let canonical := wordCanonicalizeMoves moves
      let m2 := canonical.foldl (fun acc m => acc + m.count + m.maxPriority) 0
      let _ ← force m2
      let h3 ← IO.monoMsNow
      let costed := canonical.map (wordCoalesceMoveCost spillCosts)
      let m3 := costed.foldl (fun acc m => acc + m.priority) 0
      let _ ← force m3
      let h4 ← IO.monoMsNow
      let chk := chk + m0 + m1 + m2 + m3
      heurWalk rest (index + 1) (tm + (h1 - h0)) (tsc + (h2 - h1))
        (tcanon + (h3 - h2)) (tcost + (h4 - h3)) chk

/-- Aggregate the allocator phases across every function of a program. -/
partial def phaseWalk
    (entries : List (Nat × Nat × WordProg (RiscV.Word 64))) (index : Nat)
    (tp tc ts th tm ti tf ta tr te chk : Nat) : IO Unit := do
  match entries with
  | [] =>
      IO.println s!"PERF phases preprocess {tp} | clashTree(lazy) {tc} | stackOnlyForced {ts} | heuristics {th} | clashTree+mkBij {tm} | initRaState {ti} | filterMoves+initHeu {tf} | rptDoStep {ta} | resort+assign {tr} | extractColor {te} | checksum {chk}"
  | (label, arity, body) :: rest => do
      let wordParameters := wordSsaAbiParameters arity
      let unallocatedBody := RiscV.wordRemoveUnreachable (wordProgDCE
        (RiscV.wordInstSelectProgramFrom
          (RiscV.wordFuseConditionsAndFold
            (RiscV.wordConstFp (RiscV.wordFlattenProgramFrom body)))))
      let p0 ← IO.monoMsNow
      let (_, _, ssa0) := wordFullSsaCcTrans wordParameters.length unallocatedBody
      let ssaProgram := RiscV.wordRemoveDeadProgram (RiscV.wordRemoveUnreachableAfterCopy
        (RiscV.wordThreeToTwoReg (RiscV.wordCopyProp (RiscV.wordCseProp
          (RiscV.wordRemoveDeadProgram ssa0)))))
      let chk := chk + countWord ssaProgram
      let p1 ← IO.monoMsNow
      let tree := wordClashTree ssaProgram []
      let p2 ← IO.monoMsNow
      let fs := RiscV.CakeRegAlloc.cakeGetStackOnly ssaProgram
      let forced := RiscV.CakeRegAlloc.cakeGetForced ssaProgram
      let chk := chk + fs.length + forced.length
      let p3 ← IO.monoMsNow
      let (wordMoves, spillCosts) := wordGetHeuristics 3 label ssaProgram
      let moves := wordMoves.map (fun m => (m.priority, (m.left, m.right)))
      let chk := chk + moves.length
      let p4 ← IO.monoMsNow
      let bij := RiscV.CakeRegAlloc.cakeMkBij tree
      let chk := chk + bij.nextNode
      let p5 ← IO.monoMsNow
      let state0 := RiscV.CakeRegAlloc.cakeInitRaStateFromBij bij tree forced fs
      let chk := chk + state0.dim + state0.adjLists.slots.size
      let p6 ← IO.monoMsNow
      let k := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
      let scost := spillCosts.map (fun costs =>
        RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap bij.nextNode
          (costs.filterMap (fun entry =>
            (lookupNatInfo entry.1 bij.toAllocator).map (fun node => (node, entry.2)))))
      let spta := fun v => (RiscV.CakeRegAlloc.cakeMapLookup bij.toAllocator v).getD 0
      let moves0 := moves.map (RiscV.CakeRegAlloc.cakeUpdateMove spta)
      let movesF := RiscV.CakeRegAlloc.filterReversed
        (fun m => RiscV.CakeRegAlloc.cakeFullConsistencyOk state0 k m.2.1 m.2.2) moves0
      let (l, s0) := RiscV.CakeRegAlloc.cakeInitAlloc1Heu movesF k state0
      let chk := chk + l + movesF.length
      let p7 ← IO.monoMsNow
      let s1 := RiscV.CakeRegAlloc.cakeRptDoStep scost k l s0
      let chk := chk + s1.stack.length
      let p8 ← IO.monoMsNow
      let mvs := RiscV.CakeRegAlloc.cakeResortMovesSp
        (RiscV.CakeRegAlloc.cakeMovesToSp moves0
          (RiscV.CakeRegAlloc.CakeNodeMap.ofSize bij.nextNode))
      let st2 := RiscV.CakeRegAlloc.cakeAssignAtemps k s1.stack
        (fun s n ks => RiscV.CakeRegAlloc.cakeBiasedPref s mvs n ks) s1
      let st3 := RiscV.CakeRegAlloc.cakeAssignStemps k
        (fun s n bads => RiscV.CakeRegAlloc.cakeNegBiasedPref s k mvs n bads) st2
      let chk := chk + st3.stack.length + mvs.toNatInfoMap.length
      let p9 ← IO.monoMsNow
      let colours := RiscV.CakeRegAlloc.cakeExtractColor st3 bij.toAllocator
      let chk := chk + colours.length
      let p10 ← IO.monoMsNow
      phaseWalk rest (index + 1) (tp + (p1 - p0)) (tc + (p2 - p1)) (ts + (p3 - p2))
        (th + (p4 - p3)) (tm + (p5 - p4)) (ti + (p6 - p5)) (tf + (p7 - p6))
        (ta + (p8 - p7)) (tr + (p9 - p8)) (te + (p10 - p9)) chk

def main : IO Unit := do
  let some input ← IO.getEnv "PERF_INPUT"
    | do IO.eprintln "PERF_INPUT not set"; return
  let entryName := (← IO.getEnv "PERF_ENTRY").getD "main"
  let source ← IO.FS.readFile input
  IO.println s!"PERF sourceBytes {source.length} entry={entryName}"
  if (← IO.getEnv "PERF_FULL").isSome then
    let f0 ← IO.monoMsNow
    match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
        (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] perfRemoveConfig "main" source with
    | .error error => IO.println s!"PERF full FAILED {repr error}"
    | .ok image =>
        let f1 ← stage "full:runtimeImage" f0 image.sections.length
        let assembly := RiscV.pancakeRuntimeAssembly image.crepe image
        let _ ← stage "full:assembly" f1 assembly.length
        pure ()
  let tl0 ← IO.monoMsNow
  let chars := source.toList
  let tl1 ← stage "String.toList" tl0 chars.length
  match Parser.safePancakeLex source with
  | .error errors => IO.println s!"PERF lex FAILED {errors.length}"
  | .ok tokens => do
      let _ ← stage "safePancakeLex" tl1 tokens.length
      pure ()
  let t0 ← IO.monoMsNow
  match Parser.parseTopDecs (fun value : Int => BitVec.ofInt 64 value) source with
  | .error errors => IO.println s!"PERF parse FAILED {errors.length}"
  | .ok parsed =>
      let t1 ← stage "parse" t0 parsed.length
      let checked := staticCheck parsed
      let t1 ← stage "staticCheck" t1 ((checked.1.toOption.map (fun _ => 0)).getD 1 + checked.2.length)
      let declarations := panTargetDeclarationsWithDefaultMain parsed
      let declarations := panTargetMoveStartToFront entryName declarations
      let t2 ← stage "moveStart" t1 declarations.length
      let simplified := panSimpDecls declarations
      let t3 ← stage "panSimpDecls" t2 (countDecls simplified)
      let structured := structCompileTop simplified
      let t4 ← stage "structCompileTop" t3 (countDecls structured)
      match pipelineFindFunction entryName structured with
      | none => IO.println "PERF entry NOT FOUND"
      | some entry =>
          let renamed := globalNewMainName structured
          let prepared := globalRenameDecls entryName renamed (globalResortDecls structured)
          let t5 ← stage "globalRename" t4 (countDecls prepared)
          let globals0 := globalCompileTop (BitVec.ofNat 64 8)
            (fun value => BitVec.ofNat 64 value) prepared
          let t6 ← stage "globalCompileTop" t5 (countDecls globals0.declarations)
          let entryArguments := entry.params.map (fun parameter =>
            Exp.var .local parameter.1)
          let wrapper : Decl (BitVec 64) := .function
            { name := entryName
              inline := false
              exported := false
              params := entry.params
              body := .seq (nestedSeq globals0.initializers)
                (.call none renamed entryArguments)
              returnShape := entry.returnShape }
          let globals := { globals0 with declarations := wrapper :: globals0.declarations }
          let crepeContext := pipelineCrepeCompileContext
            (fun value => BitVec.ofNat 64 value) globals
          let compiled := compileToCrepFixed crepeContext globals.declarations
          let t7 ← stage "compileToCrep" t6 (countCrepFunctions compiled)
          let inlined := crepInlineTopRecursiveByNames
            (pipelineInlineNames globals.declarations) compiled
          let t8 ← stage "crepInline" t7 (countCrepFunctions inlined)
          let crepe := crepSimpFunctions (fun value => BitVec.ofNat 64 value) inlined
          let t9 ← stage "crepSimp" t8 (countCrepFunctions crepe)
          let loop := pipelineLoopFunctionsSource .rv64i 1 crepe
          let t10 ← stage "crepToLoop" t9
            (loop.foldl (fun acc (_, _, body) => acc + countLoop body) 0)
          let word := pipelineWordFunctionsSource loop
          let _ ← stage "loopToWord" t10
            (word.foldl (fun acc (_, _, body) => acc + countWord body) 0)
          IO.println s!"PERF functions loop={loop.length} word={word.length}"
          if (← IO.getEnv "PERF_LOWERFAIL").isSome then
            let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
            let sourceWords := panToWordCompileProg sourceLoop
            let target := (← IO.getEnv "PERF_LOWERFAIL").getD "0" |>.toNat!
            match sourceWords.drop target with
            | [] => IO.println "PERF lowerfail: index out of range"
            | (label, arity, body) :: _ => do
                let wordParameters := wordSsaAbiParameters arity
                let unallocatedBody := RiscV.wordRemoveUnreachable (wordProgDCE
                  (RiscV.wordInstSelectProgramFrom
                    (RiscV.wordFuseConditionsAndFold
                      (RiscV.wordConstFp (RiscV.wordFlattenProgramFrom body)))))
                match RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead
                    label wordParameters unallocatedBody with
                | none => IO.println "PERF lowerfail: allocation failed"
                | some (_, renamedParameters, renamedProgram, allocation) => do
                    let renamedProgram := RiscV.wordProgReverseFfiConstSetup renamedProgram
                    let frameSlots :=
                      RiscV.cakeWordFrameSlots allocation wordParameters renamedProgram
                    let config : RiscV.WordStackConfig :=
                      { locations := allocation.locations
                        scratch := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
                        stackBase := 0
                        addressScratch := 23
                        specialScratch := RiscV.cakeSpecialScratch
                        carryScratch := RiscV.cakeCarryScratch
                        abiBase := 1
                        abiStride := 1
                        callAbiBase := 0
                        abiFrameSlots := frameSlots
                        sectionId := label
                        handlerLabel := label }
                    let natProgram := RiscV.wordProgToNat renamedProgram
                    IO.println s!"PERF lowerfail label={label} frameSlots={frameSlots} params={renamedParameters.length} nodes={countWord renamedProgram}"
                    IO.println s!"PERF lowerfail firstUnsupported={repr (RiscV.wordProgFirstUnsupported natProgram)}"
                    IO.println s!"PERF lowerfail firstExprFailure={repr (RiscV.wordProgFirstExpressionLoweringFailure config natProgram)}"
                    let plain := RiscV.wordToStackProgNat config natProgram
                    IO.println s!"PERF lowerfail plainNat={plain.isSome}"
                    let localState : RiscV.WordStackBitmapState := { data := [], length := 0 }
                    let fused := RiscV.wordToStackProgWordWithLocationBitmapsFused config
                      RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch frameSlots 64
                      (some 1) localState renamedProgram
                    IO.println s!"PERF lowerfail fused={fused.isSome}"
                    if plain.isNone then
                      let (path, culprit) := findLowerFailure config [] natProgram
                      IO.println s!"PERF lowerfail path={path}"
                      IO.println s!"PERF lowerfail culprit={(repr culprit).pretty.take 1500}"
                      match culprit with
                      | .inst (.arith (.addCarry d rc sl sr ci)) =>
                          let loc n := repr (RiscV.wordStackLocation config n)
                          IO.println s!"PERF lowerfail addCarry dest={d}@{loc d} carry={rc}@{loc rc} left={sl}@{loc sl} right={sr}@{loc sr} carryIn={ci}@{loc ci}"
                          IO.println s!"PERF lowerfail scratch={config.scratch} addressScratch={config.addressScratch} specialScratch={config.specialScratch} carryScratch={config.carryScratch}"
                      | _ => pure ()
                    (← IO.getStdout).flush
          if (← IO.getEnv "PERF_ALLOCSUB").isSome then
            let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
            let sourceWords := panToWordCompileProg sourceLoop
            let target := (← IO.getEnv "PERF_ALLOCSUB").getD "0" |>.toNat!
            match sourceWords.drop target with
            | [] => IO.println "PERF allocsub: index out of range"
            | (label, arity, body) :: _ => do
                let wordParameters := wordSsaAbiParameters arity
                let unallocatedBody := RiscV.wordRemoveUnreachable (wordProgDCE
                  (RiscV.wordInstSelectProgramFrom
                    (RiscV.wordFuseConditionsAndFold
                      (RiscV.wordConstFp (RiscV.wordFlattenProgramFrom body)))))
                let a0 ← IO.monoMsNow
                let (_, _, ssa0) := wordFullSsaCcTrans wordParameters.length unallocatedBody
                let pp1 ← stage "pp:fullSsaCcTrans" a0 (countWord ssa0)
                let ssa1 := RiscV.wordRemoveDeadProgram ssa0
                let pp2 ← stage "pp:removeDead1" pp1 (countWord ssa1)
                let ssa2 := RiscV.wordCseProp ssa1
                let pp3 ← stage "pp:cseProp" pp2 (countWord ssa2)
                let ssa3 := RiscV.wordCopyProp ssa2
                let pp4 ← stage "pp:copyProp" pp3 (countWord ssa3)
                let ssa4 := RiscV.wordThreeToTwoReg ssa3
                let pp5 ← stage "pp:threeToTwo" pp4 (countWord ssa4)
                let ssa5 := RiscV.wordRemoveUnreachableAfterCopy ssa4
                let pp6 ← stage "pp:removeUnreach" pp5 (countWord ssa5)
                let ssaProgram := RiscV.wordRemoveDeadProgram ssa5
                let a1 ← stage "pp:removeDead2" pp6 (countWord ssaProgram)
                let tree := wordClashTree ssaProgram []
                let a2 ← stage "as:clashTree" a1 (countWord ssaProgram)
                let fs := RiscV.CakeRegAlloc.cakeGetStackOnly ssaProgram
                let forced := RiscV.CakeRegAlloc.cakeGetForced ssaProgram
                let a3 ← stage "as:stackOnlyForced" a2 (fs.length + forced.length)
                let (wordMoves, spillCosts) := wordGetHeuristics 3 label ssaProgram
                let moves := wordMoves.map (fun m => (m.priority, (m.left, m.right)))
                let a4 ← stage "as:heuristics" a3 moves.length
                let bij := RiscV.CakeRegAlloc.cakeMkBij tree
                let a5 ← stage "as:mkBij" a4 bij.nextNode
                let scost := spillCosts.map (fun costs =>
                  RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap bij.nextNode
                    (costs.filterMap (fun entry =>
                      (lookupNatInfo entry.1 bij.toAllocator).map (fun node => (node, entry.2)))))
                let k := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
                let state0 := RiscV.CakeRegAlloc.cakeInitRaStateFromBij bij tree forced fs
                let edges := state0.adjLists.toNatInfoMap.foldl
                  (fun acc entry => acc + entry.2.length) 0
                let a6 ← stage "as:initRaState" a5 edges
                IO.println s!"PERF allocsub label={label} nodes={bij.nextNode} edges={edges} moves={moves.length} fs={fs.length} forced={forced.length}"
                (← IO.getStdout).flush
                let spta := fun v => (RiscV.CakeRegAlloc.cakeMapLookup bij.toAllocator v).getD 0
                let moves0 := moves.map (RiscV.CakeRegAlloc.cakeUpdateMove spta)
                let movesF := RiscV.CakeRegAlloc.filterReversed
                  (fun m => RiscV.CakeRegAlloc.cakeFullConsistencyOk state0 k m.2.1 m.2.2) moves0
                let a7 ← stage "as:filterMoves" a6 movesF.length
                let (l, s0) := RiscV.CakeRegAlloc.cakeInitAlloc1Heu movesF k state0
                let a8 ← stage "as:initAlloc1Heu" a7 l
                let s1 ← if (← IO.getEnv "PERF_STEPS").isSome then
                    timedRpt scost k l s0 0 0 0 0 0 0 0 0 0 0
                  else pure (RiscV.CakeRegAlloc.cakeRptDoStep scost k l s0)
                let a9 ← stage "as:rptDoStep" a8 s1.stack.length
                let mvs := RiscV.CakeRegAlloc.cakeResortMovesSp
                  (RiscV.CakeRegAlloc.cakeMovesToSp moves0
          (RiscV.CakeRegAlloc.CakeNodeMap.ofSize bij.nextNode))
                let a10 ← stage "as:resortMoves" a9 mvs.toNatInfoMap.length
                let st2 := RiscV.CakeRegAlloc.cakeAssignAtemps k s1.stack
                  (fun s n ks => RiscV.CakeRegAlloc.cakeBiasedPref s mvs n ks) s1
                let a11 ← stage "as:assignAtemps" a10 st2.stack.length
                let st3 := RiscV.CakeRegAlloc.cakeAssignStemps k
                  (fun s n bads => RiscV.CakeRegAlloc.cakeNegBiasedPref s k mvs n bads) st2
                let a12 ← stage "as:assignStemps" a11 st3.stack.length
                let colours := RiscV.CakeRegAlloc.cakeExtractColor st3 bij.toAllocator
                let _ ← stage "as:extractColor" a12 colours.length
                pure ()
          if (← IO.getEnv "PERF_HEURWALK").isSome then
            let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
            let sourceWords := panToWordCompileProg sourceLoop
            heurWalk sourceWords 0 0 0 0 0 0
          if (← IO.getEnv "PERF_SPLIT").isSome then
            let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
            let sourceWords := panToWordCompileProg sourceLoop
            let s0 ← IO.monoMsNow
            match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
                (RiscV.wordStackInitialBitmaps false) sourceWords with
            | Except.error _ => IO.println "PERF split backend FAILED"
            | Except.ok (stackFunctions, _) =>
                let _ ← force (stackFunctions.foldl (fun acc entry => acc + entry.1) 0)
                let _ ← stage "split:wordToStackBackend" s0 stackFunctions.length
                pure ()
          if (← IO.getEnv "PERF_LAB").isSome then
            let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
            let sourceWords := panToWordCompileProg sourceLoop
            match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
                (RiscV.wordStackInitialBitmaps false) sourceWords with
            | Except.error _ => IO.println "PERF lab backend FAILED"
            | Except.ok (stackFunctions, _) =>
                let initialLabel := fullSsaInitialLabLabel stackFunctions
                let programs := stackFunctions.map (fun entry => (entry.1, entry.2.2))
                let config := RiscV.cakeStackRemoveConfig perfRemoveConfig
                let programs :=
                  (stackRaiseStubLocation,
                    stackRaiseStub false config.addressScratch) :: programs
                match RiscV.stackProgramsWithLongDivRuntime config programs with
                | none => IO.println "PERF lab longdiv FAILED"
                | some programs =>
                    let programs := stackRawCallPrograms programs
                    let l0 ← IO.monoMsNow
                    let labProgram : List (LabSection (RiscV.Word 64)) :=
                      (programs.map (fun (sectionId, program) =>
                        labProgramToEntrySection sectionId 0 initialLabel
                          (stackMapRegisters RiscV.riscvRegisterName
                            (stackRemoveComplete config program)))).map
                        RiscV.labSectionNatToWord
                    let lineCount := labProgram.foldl
                      (fun acc (sectionData : LabSection (RiscV.Word 64)) =>
                        acc + sectionData.lines.length) 0
                    let _ ← force lineCount
                    let l1 ← stage "lab:build" l0 lineCount
                    -- Faithful copy of compileLabProgramLinkedWithPancakeRuntime,
                    -- timed between each of its lets.
                    let context : RiscV.WordFfiContext := { services := [] }
                    let sourceProgram := labProgram.filter
                      (fun (sectionData : LabSection (RiscV.Word 64)) =>
                        sectionData.name >= 3)
                    let initial := RiscV.labInitialStoredProgram sourceProgram
                    let _ ← force (RiscV.labStoredProgramLength initial)
                    let l2 ← stage "lab:initialStored" l1
                      (RiscV.labStoredProgramLength initial)
                    let initialHaltPc := 1000 + RiscV.labStoredProgramLength initial
                    let encoded := RiscV.labEncodeStoredProgramStable 8 context 1000 1000
                      initialHaltPc initial
                    let _ ← force (RiscV.labStoredProgramLength encoded)
                    let l3 ← stage "lab:encodeStable" l2
                      (RiscV.labStoredProgramLength encoded)
                    let relabelled := RiscV.labUpdateStoredLabelLengths 1000 encoded
                    let _ ← force (RiscV.labStoredProgramLength relabelled)
                    let l4 ← stage "lab:updateLabelLengths" l3
                      (RiscV.labStoredProgramLength relabelled)
                    let haltPc := 1000 + RiscV.labStoredProgramLength relabelled
                    let relabelledLabels := RiscV.labLabelIndexOf
                      (RiscV.labCollectPancakeRuntimeStoredLabels relabelled)
                    let _ ← force relabelledLabels.entries.length
                    let l5 ← stage "lab:collectRelabelled" l4
                      relabelledLabels.entries.length
                    let final := RiscV.labEncodeStoredProgram context relabelledLabels
                      1000 1000 haltPc relabelled
                    let _ ← force (RiscV.labStoredProgramLength final)
                    let l6 ← stage "lab:encodeFinal" l5
                      (RiscV.labStoredProgramLength final)
                    let labels := RiscV.labLabelIndexOf
                      (RiscV.labCollectPancakeRuntimeStoredLabels final)
                    let _ ← force labels.entries.length
                    let l7 ← stage "lab:collectFinal" l6 labels.entries.length
                    let labAsmCount := final.foldl
                      (fun acc (sectionData : LabSection (RiscV.Word 64)) =>
                        acc + sectionData.lines.foldl (fun n line =>
                          match line with
                          | .labAsm _ _ _ => n + 1
                          | _ => n) 0) 0
                    let _ ← force labAsmCount
                    IO.println s!"PERF lab labAsmLines {labAsmCount} labels {labels.entries.length}"
                    match RiscV.compileLabProgramLinkedWithStoredLengthsAux
                        context labels 1000 1000 haltPc final with
                    | none => IO.println "PERF lab link FAILED"
                    | some sections =>
                        let _ ← force (sections.foldl
                          (fun acc (entry : Nat × RiscV.Word 64 × List (RiscV.Instruction 64)) =>
                            acc + entry.2.2.length) 0)
                        let l8 ← stage "lab:linkEmit" l7 sections.length
                        let encodedSections := RiscV.encodeLinkedSections sections
                        let _ ← force encodedSections.length
                        let _ ← stage "lab:encodeSections" l8 encodedSections.length
                        pure ()
          if (← IO.getEnv "PERF_PHASEWALK").isSome then
            let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
            let sourceWords := panToWordCompileProg sourceLoop
            phaseWalk sourceWords 0 0 0 0 0 0 0 0 0 0 0 0
          if (← IO.getEnv "PERF_IMAGEWALK").isSome then
            let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
            let sourceWords := panToWordCompileProg sourceLoop
            let from_ := (← IO.getEnv "PERF_IMAGEWALK_FROM").getD "0" |>.toNat!
            let count := (← IO.getEnv "PERF_IMAGEWALK_COUNT").getD "100000" |>.toNat!
            imageWalk ((sourceWords.drop from_).take count) from_
          if (← IO.getEnv "PERF_FRAME").isSome then
            let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
            let sourceWords := panToWordCompileProg sourceLoop
            let limit := (← IO.getEnv "PERF_FRAME_COUNT").getD "100000" |>.toNat!
            frameWalk (sourceWords.take limit) 0
          if (← IO.getEnv "PERF_SUB").isSome then
            let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
            let sourceWords := panToWordCompileProg sourceLoop
            let target := (← IO.getEnv "PERF_SUB").getD "0" |>.toNat!
            match sourceWords.drop target with
            | [] => IO.println "PERF sub: index out of range"
            | (label, arity, body) :: _ => do
                IO.println s!"PERF sub target label={label} arity={arity} size={countWord body}"
                let s0 ← IO.monoMsNow
                let wordParameters := wordSsaAbiParameters arity
                let flattened := RiscV.wordFlattenProgramFrom body
                let s1 ← stage "sub:flatten" s0 (countWord flattened)
                let constFp := RiscV.wordConstFp flattened
                let s2 ← stage "sub:constFp" s1 (countWord constFp)
                let selected := RiscV.wordInstSelectProgramFrom constFp
                let s3 ← stage "sub:instSelect" s2 (countWord selected)
                let fused := RiscV.wordFuseConditions selected
                let s4 ← stage "sub:fuseConditions" s3 (countWord fused)
                let dced := wordProgDCE fused
                let s5 ← stage "sub:dce" s4 (countWord dced)
                let unallocatedBody := RiscV.wordRemoveUnreachable dced
                let s6 ← stage "sub:removeUnreachable" s5 (countWord unallocatedBody)
                match RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDead
                    label wordParameters unallocatedBody with
                | none => IO.println "PERF sub:allocate FAILED"
                | some (_, renamedParameters, renamedProgram, allocation) => do
                    let s7 ← stage "sub:cakeAllocateWordFunctionAfterDead" s6
                      (countWord renamedProgram)
                    -- break cakeAllocateWordFunctionAfterDead down
                    let a0 ← IO.monoMsNow
                    let (_, _, ssa0) := wordFullSsaCcTrans wordParameters.length unallocatedBody
                    let a1 ← stage "alloc:fullSsaCcTrans" a0 (countWord ssa0)
                    let ssa1 := RiscV.wordRemoveDeadProgram ssa0
                    let a2 ← stage "alloc:removeDead1" a1 (countWord ssa1)
                    let ssa2 := RiscV.wordCseProp ssa1
                    let a3 ← stage "alloc:cseProp" a2 (countWord ssa2)
                    let ssa3 := RiscV.wordCopyProp ssa2
                    let a4 ← stage "alloc:copyProp" a3 (countWord ssa3)
                    let ssa4 := RiscV.wordThreeToTwoReg ssa3
                    let a5 ← stage "alloc:threeToTwoReg" a4 (countWord ssa4)
                    let ssa5 := RiscV.wordRemoveUnreachableAfterCopy ssa4
                    let a6 ← stage "alloc:removeUnreachable" a5 (countWord ssa5)
                    let ssaProg := RiscV.wordRemoveDeadProgram ssa5
                    let a7 ← stage "alloc:removeDead2" a6 (countWord ssaProg)
                    let tree2 := wordClashTree ssaProg []
                    let a8 ← stage "alloc:clashTree" a7 (s!"{repr tree2}").length
                    let fs2 := RiscV.CakeRegAlloc.cakeGetStackOnly ssaProg
                    let a9 ← stage "alloc:getStackOnly" a8 fs2.length
                    let forced2 := RiscV.CakeRegAlloc.cakeGetForced ssaProg
                    let a10 ← stage "alloc:getForced" a9 forced2.length
                    let (wm2, sc2) := wordGetHeuristics 3 label ssaProg
                    let a11 ← stage "alloc:getHeuristics(fast)" a10
                      (wm2.length + (sc2.map List.length).getD 0)
                    let bij2 := RiscV.CakeRegAlloc.cakeMkBij tree2
                    let a12 ← stage "alloc:mkBij" a11 bij2.toAllocator.length
                    let moves2 := wm2.map (fun m => (m.priority, (m.left, m.right)))
                    let scost2 := sc2.map (fun costs =>
                      RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap bij2.nextNode
                        (costs.filterMap (fun entry =>
                          (lookupNatInfo entry.1 bij2.toAllocator).map
                            (fun node => (node, entry.2)))))
                    match RiscV.CakeRegAlloc.cakeDoRegAlloc .irc scost2
                        RiscV.CakeRegAlloc.cakeRiscVRegisterCount moves2 tree2 forced2 fs2 with
                    | none => IO.println "PERF alloc:doRegAlloc FAILED"
                    | some colouring2 => do
                        let a13 ← stage "alloc:cakeDoRegAlloc" a12 (s!"{repr colouring2}").length
                        let _ ← stage "alloc:spillState" a13
                          (RiscV.CakeRegAlloc.cakeColourWordSpillState
                            RiscV.CakeRegAlloc.cakeRiscVRegisterCount
                            wordParameters ssaProg colouring2).nextSpill
                        pure ()
                    let renamedProgram := RiscV.wordProgReverseFfiConstSetup renamedProgram
                    let s8 ← stage "sub:reverseFfiConstSetup" s7 (countWord renamedProgram)
                    let unflattenedBody := wordProgDCE (RiscV.wordFuseConditions body)
                    let cakeFrameSlots :=
                      if RiscV.wordProgHasBitmapSites renamedProgram then
                        RiscV.CakeRegAlloc.cakeWordStackVarCount label wordParameters
                          RiscV.CakeRegAlloc.cakeRiscVRegisterCount unflattenedBody
                      else 0
                    let frameSlots := max cakeFrameSlots
                      (max (wordParameters.length - 12)
                        (RiscV.wordProgMaxCallArguments renamedProgram - 12))
                    let s9 ← stage "sub:frameSlots" s8 frameSlots
                    -- break cakeWordStackVarCount down
                    if RiscV.wordProgHasBitmapSites renamedProgram then do
                      let v0 ← IO.monoMsNow
                      let ssaProgram := (wordFullSsaCcTrans wordParameters.length unflattenedBody).2.2
                      let v1 ← stage "var:fullSsaCcTrans" v0 (countWord ssaProgram)
                      let tree := wordClashTree ssaProgram []
                      let v2 ← stage "var:clashTree" v1 (s!"{repr tree}").length
                      let fs := RiscV.CakeRegAlloc.cakeGetStackOnly ssaProgram
                      let v3 ← stage "var:getStackOnly" v2 fs.length
                      let forced := RiscV.CakeRegAlloc.cakeGetForced ssaProgram
                      let v4 ← stage "var:getForced" v3 forced.length
                      let rawMoves := wordProgPrioritizedMoves ssaProgram
                      let vh1 ← stage "var:h.prioritizedMoves" v4 rawMoves.length
                      let heuristicResult := wordHeuristic label ssaProgram ([], [])
                      let vh2 ← stage "var:h.wordHeuristic" vh1
                        (heuristicResult.1.length + heuristicResult.2.length)
                      let rawSpillCosts := wordHeuristicSpillCosts label ssaProgram
                      let vh3 ← stage "var:h.spillCostsMap" vh2 rawSpillCosts.length
                      let sortedMoves := wordSortPriorityMoves (rawMoves.map wordCanonicalPriorityMove)
                      let vh4 ← stage "var:h.sortMoves" vh3 sortedMoves.length
                      let canonical := wordCanonicalizeMoves rawMoves
                      let _ ← stage "var:h.canonicalize" vh4 canonical.length
                      let (wordMoves, spillCosts) := wordGetHeuristics 3 label ssaProgram
                      let v5 ← stage "var:heuristics" v4 (wordMoves.length + (spillCosts.map List.length).getD 0)
                      let moves := wordMoves.map (fun m => (m.priority, (m.left, m.right)))
                      let bij := RiscV.CakeRegAlloc.cakeMkBij tree
                      let v6 ← stage "var:mkBij" v5 bij.toAllocator.length
                      let scost := spillCosts.map (fun costs =>
                        RiscV.CakeRegAlloc.CakeNodeMap.ofNatInfoMap bij.nextNode
                          (costs.filterMap (fun entry =>
                            (lookupNatInfo entry.1 bij.toAllocator).map
                              (fun node => (node, entry.2)))))
                      let v7 ← stage "var:spillCosts" v6
                        ((scost.map (fun m => m.toNatInfoMap.length)).getD 0)
                      match RiscV.CakeRegAlloc.cakeDoRegAlloc .irc scost
                          RiscV.CakeRegAlloc.cakeRiscVRegisterCount moves tree forced fs with
                      | none => IO.println "PERF var:doRegAlloc FAILED"
                      | some colouring => do
                          let v8 ← stage "var:cakeDoRegAlloc" v7 (s!"{repr colouring}").length
                          let colour := RiscV.CakeAlloc.totalColour colouring
                          let coloured := wordApplyColour colour ssaProgram
                          let v9 ← stage "var:applyColour" v8 (countWord coloured)
                          let maxVar := (wordProgVariables coloured).foldl max 0
                          let _ ← stage "var:wordProgVariables" v9 maxVar
                          pure ()
                    let config : RiscV.WordStackConfig :=
                      { locations := allocation.locations
                        scratch := RiscV.CakeRegAlloc.cakeRiscVRegisterCount
                        stackBase := 0
                        addressScratch := 23
                        specialScratch := RiscV.cakeSpecialScratch
                        carryScratch := RiscV.cakeCarryScratch
                        abiBase := 1
                        abiStride := 1
                        callAbiBase := 0
                        abiFrameSlots := frameSlots
                        sectionId := label
                        handlerLabel := label }
                    let localState : RiscV.WordStackBitmapState :=
                      { data := [], length := 0 }
                    let lower :=
                      if frameSlots = 0 then
                        RiscV.wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMovesWithSources
                          config renamedParameters wordRiscVAbiSourceRegister
                          RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch
                          frameSlots (some 1) localState renamedProgram
                      else
                        RiscV.wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMovesWithSources
                          config renamedParameters wordRiscVAbiSourceRegister
                          RiscV.CakeRegAlloc.cakeRiscVRegisterCount config.scratch
                          frameSlots (some 1) localState renamedProgram
                    match lower with
                    | none => IO.println "PERF sub:wordToStack FAILED"
                    | some (stackBody, _) =>
                        let _ ← stage "sub:wordToStack" s9 (sizeOf stackBody.ctorIdx)
                        pure ()
          if (← IO.getEnv "PERF_IMAGE").isSome then
            let ti0 ← IO.monoMsNow
            let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
            let sourceWords := panToWordCompileProg sourceLoop
            let ti1 ← stage "image:sourceWords" ti0
              (sourceWords.foldl (fun acc (_, _, body) => acc + countWord body) 0)
            let discoveredNames :=
              (sourceWords.flatMap
                (fun entry : Nat × Nat × WordProg (RiscV.Word 64) =>
                  RiscV.wordProgFfiNames (RiscV.wordRemoveUnreachable (wordProgDCE entry.2.2)))).eraseDups
            let ti2 ← stage "image:ffiDiscovery" ti1 discoveredNames.length
            let services := discoveredNames.zip (List.range discoveredNames.length)
            match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
                (RiscV.wordStackInitialBitmaps false) sourceWords with
            | .error _ => IO.println "PERF image:allocate FAILED"
            | .ok (functions, bitmaps) =>
                let ti3 ← stage "image:allocateAndStack" ti2
                  (functions.length + bitmaps.length)
                let initialLabel := fullSsaInitialLabLabel functions
                let ti4 ← stage "image:initialLabel" ti3 initialLabel
                match RiscV.compileStackProgramNatListLinkedWithSimpleGcAndStoreConstsToRiscVCakeChecked
                    (width := 64) { services := services } perfRemoveConfig
                    { gcStubLocation := stackGcStubLocation, returnLabel := 0,
                      firstFreshLabel := stackFunctionFirstLabel }
                    { } stackStoreConstsStubLocation RiscV.CakeRegAlloc.cakeRiscVRegisterCount
                    0 initialLabel
                    (functions.map (fun (label, _, body) => (label, body))) with
                | .error _ => IO.println "PERF image:lab FAILED"
                | .ok sections =>
                    let ti5 ← stage "image:labToRiscV" ti4
                      (sections.foldl (fun acc (_, _, code) => acc + code.length) 0)
                    let encoded := RiscV.encodeLinkedSections sections
                    let ti6 ← stage "image:encode" ti5 encoded.length
                    let image : SourceRiscVRuntimeImage 64 :=
                      { crepe := crepe, bitmaps := bitmaps, sections := encoded,
                        warnings := [], ffiNames := discoveredNames }
                    let assembly := RiscV.pancakeRuntimeAssembly crepe image
                    let _ ← stage "image:pancakeRuntimeAssembly" ti6 assembly.length
                    pure ()
          if (← IO.getEnv "PERF_DISCOVERY").isSome then
            let td0 ← IO.monoMsNow
            let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel crepe
            let sourceWords := panToWordCompileProg sourceLoop
            let td1 ← stage "sourceWords" td0
              (sourceWords.foldl (fun acc (_, _, body) => acc + countWord body) 0)
            -- current shape: an extra whole-program DCE pass whose result is
            -- then DCE'd again inside the FFI-name scan
            let discoveryWords :=
              sourceWords.map (fun (label, arity, body) => (label, arity, wordProgDCE body))
            let td2 ← stage "discoveryWords(extra DCE)" td1
              (discoveryWords.foldl (fun acc (_, _, body) => acc + countWord body) 0)
            let namesDouble :=
              (discoveryWords.flatMap
                (fun entry : Nat × Nat × WordProg (RiscV.Word 64) =>
                  RiscV.wordProgFfiNames (RiscV.wordRemoveUnreachable (wordProgDCE entry.2.2)))).eraseDups
            let td3 ← stage "ffiNames(from discoveryWords)" td2 namesDouble.length
            let namesSingle :=
              (sourceWords.flatMap
                (fun entry : Nat × Nat × WordProg (RiscV.Word 64) =>
                  RiscV.wordProgFfiNames (RiscV.wordRemoveUnreachable (wordProgDCE entry.2.2)))).eraseDups
            let _ ← stage "ffiNames(from sourceWords)" td3 namesSingle.length
            IO.println s!"PERF ffiNamesEqual {namesDouble == namesSingle}"
            -- faithful copy of the real discovery in
            -- compileFlapjackRiscVSourceRuntimeImageChecked
            let td4 ← IO.monoMsNow
            let realNames :=
              (discoveryWords.reverse.flatMap
                (fun entry : Nat × Nat × WordProg (RiscV.Word 64) =>
                  RiscV.wordProgFfiNamesCake (wordFfiDiscoveryBody entry.2.2))).eraseDups
            let _ ← force realNames.length
            let _ ← stage "ffiNames(real, wordFfiDiscoveryBody)" td4 realNames.length
            -- pass-by-pass inside wordFfiDiscoveryBody
            let bodies := discoveryWords.map (fun e => e.2.2)
            let d0 ← IO.monoMsNow
            let flat := bodies.map RiscV.wordFlattenProgramFrom
            let _ ← force (flat.foldl (fun a b => a + countWord b) 0)
            let d1 ← stage "disc:flatten" d0 (flat.foldl (fun a b => a + countWord b) 0)
            let cfp := flat.map RiscV.wordConstFp
            let _ ← force (cfp.foldl (fun a b => a + countWord b) 0)
            let d2 ← stage "disc:constFp" d1 (cfp.foldl (fun a b => a + countWord b) 0)
            let fused := cfp.map RiscV.wordFuseConditionsAndFold
            let _ ← force (fused.foldl (fun a b => a + countWord b) 0)
            let d3 ← stage "disc:fuseConditions" d2 (fused.foldl (fun a b => a + countWord b) 0)
            let sel := fused.map RiscV.wordInstSelectProgramFrom
            let _ ← force (sel.foldl (fun a b => a + countWord b) 0)
            let d4 ← stage "disc:instSelect" d3 (sel.foldl (fun a b => a + countWord b) 0)
            let dce := sel.map wordProgDCE
            let _ ← force (dce.foldl (fun a b => a + countWord b) 0)
            let d5 ← stage "disc:dce" d4 (dce.foldl (fun a b => a + countWord b) 0)
            let unreach := dce.map RiscV.wordRemoveUnreachable
            let _ ← force (unreach.foldl (fun a b => a + countWord b) 0)
            let _ ← stage "disc:removeUnreachable" d5 (unreach.foldl (fun a b => a + countWord b) 0)
            -- per-function constFp cost: is it concentrated or uniform?
            let mut worst : List (Nat × Nat × Nat) := []
            let mut idx := 0
            for b in flat do
              let c0 ← IO.monoMsNow
              let r := RiscV.wordConstFp b
              let _ ← force (countWord r)
              let c1 ← IO.monoMsNow
              worst := (c1 - c0, idx, countWord b) :: worst
              idx := idx + 1
            let top := (worst.toArray.qsort (fun a b => a.1 > b.1)).toList.take 12
            for (ms, i, size) in top do
              IO.println s!"PERF constFp fn[{i}] {ms} ms nodes={size}"
            let total := worst.foldl (fun a e => a + e.1) 0
            IO.println s!"PERF constFp totalMs {total} functions {worst.length}"
            -- split wordConstFp on the dominating function
            match flat.drop 639 with
            | [] => IO.println "PERF constFp: fn 639 missing"
            | body :: _ =>
                let a0 ← IO.monoMsNow
                let assoc := RiscV.wordSimpSeqAssoc body
                let _ ← force (countWord assoc)
                let a1 ← stage "constFp639:seqAssoc" a0 (countWord assoc)
                let (looped, _) := RiscV.wordConstFpLoop assoc ∅
                let _ ← force (countWord looped)
                let _ ← stage "constFp639:loop" a1 (countWord looped)
            IO.println s!"PERF ffiNames {namesDouble}"
          if (← IO.getEnv "PERF_BACKEND").isSome then
            let from_ := (← IO.getEnv "PERF_BACKEND_FROM").getD "0" |>.toNat!
            let count := (← IO.getEnv "PERF_BACKEND_COUNT").getD "100000" |>.toNat!
            backendWalk ((loop.drop from_).take count) from_

end Flapjack.PerfFront

def main : IO Unit := Flapjack.PerfFront.main
