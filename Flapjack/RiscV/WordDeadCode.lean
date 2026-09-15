import Flapjack.RiscV.CakeRegAlloc

/-!
# Word dead-program elimination

Cake runs `remove_dead_prog` after full SSA and before register allocation.
The port keeps the same boundary explicit here: pure definitions, moves, and
loads whose destinations are not live are removed, while stores, calls, FFI,
and the other effectful Word operations are retained.  The loop rule is
conservative, matching Cake's loop barrier by restarting the body analysis
from the loop's live-in set.
-/

namespace Flapjack.RiscV

open Flapjack

def wordDeadAddReads (live : List Nat) (reads : List Nat) : List Nat :=
  (live ++ reads).eraseDups

def wordDeadRemoveWrites (live : List Nat) (writes : List Nat) : List Nat :=
  live.filter (fun name => name ∉ writes)

def wordDeadMove (live : List Nat) (moves : List (Nat × Nat)) :
    WordProg α × List Nat :=
  let kept := moves.filter (fun move => move.1 ∈ live)
  if kept.isEmpty then
    (.skip, live)
  else
    (.move 0 kept,
      wordDeadAddReads
        (wordDeadRemoveWrites live (kept.map Prod.fst))
        (kept.map Prod.snd))

def wordDeadInst (live : List Nat) (instruction : WordInst) :
    WordProg α × List Nat :=
  let writes := wordInstWriteVars instruction
  let reads := wordInstReadVars instruction
  if writes.any (fun name => name ∈ live) then
    (.inst instruction,
      wordDeadAddReads (wordDeadRemoveWrites live writes) reads)
  else
    match instruction with
    | .mem operator _ _ =>
        match operator with
        | .store | .store8 | .store16 | .store32 =>
            (.inst instruction, wordDeadAddReads live reads)
        | _ => (.skip, live)
    | _ => (.skip, live)

def wordDeadCode : WordProg α → List Nat → WordProg α × List Nat
  | .skip, live => (.skip, live)
  | .move _ moves, live => wordDeadMove live moves
  | .assign destination value, live =>
      if destination ∈ live then
        (.assign destination value,
          wordDeadAddReads (wordDeadRemoveWrites live [destination])
            (wordExpReadVars value))
      else
        (.skip, live)
  | .inst instruction, live => wordDeadInst live instruction
  | .get destination store, live =>
      if destination ∈ live then
        (.get destination store,
          wordDeadAddReads (wordDeadRemoveWrites live [destination]) [])
      else
        (.skip, live)
  | .store address value, live =>
      (.store address value,
        wordDeadAddReads live (wordExpReadVars address ++ [value]))
  | .set store value, live =>
      (.set store value, wordDeadAddReads live (wordExpReadVars value))
  | .seq first second, live =>
      let (second', live) := wordDeadCode second live
      let (first', live) := wordDeadCode first live
      (match first', second' with
       | .skip, program => program
       | program, .skip => program
       | _, _ => .seq first' second', live)
  | .ite operator condition right thenBranch elseBranch, live =>
      let (then', thenLive) := wordDeadCode thenBranch live
      let (else', elseLive) := wordDeadCode elseBranch live
      let rightReads := match right with
        | .imm _ => []
        | .reg name => [name]
      (.ite operator condition right then' else',
        wordDeadAddReads (thenLive ++ elseLive) (condition :: rightReads))
  | .loop liveIn body liveOut, _live =>
      let (body', _) := wordDeadCode body liveIn
      (.loop liveIn body' liveOut, liveIn)
  | .mustTerminate body, live =>
      let (body', live) := wordDeadCode body live
      (.mustTerminate body', live)
  | .break label, live => (.break label, live)
  | .continue label, live => (.continue label, live)
  | .raise exception, live => (.raise exception, exception :: live)
  | .return label values, live =>
      (.return label values, wordDeadAddReads live values)
  | .tick, live => (.tick, live)
  | .locValue destination source, live =>
      if destination ∈ live then
        (.locValue destination source,
          wordDeadAddReads (wordDeadRemoveWrites live [destination]) [])
      else
        (.skip, live)
  | .call returns target arguments handler, live =>
      (.call returns target arguments handler,
        wordDeadAddReads live (wordProgReadVars
          (.call returns target arguments handler)))
  | .alloc destination cutsets, live =>
      (.alloc destination cutsets,
        wordDeadAddReads (wordDeadRemoveWrites live [destination])
          (cutsets.1 ++ cutsets.2))
  | .storeConsts source bitmap codeLength dataLength constants, live =>
      (.storeConsts source bitmap codeLength dataLength constants,
        wordDeadAddReads live [source, bitmap, codeLength, dataLength])
  | .opCurrHeap operator destination source, live =>
      (.opCurrHeap operator destination source,
        wordDeadAddReads (wordDeadRemoveWrites live [destination]) [source])
  | .install codeBuffer codeLength dataBuffer dataLength cutsets, live =>
      (.install codeBuffer codeLength dataBuffer dataLength cutsets,
        wordDeadAddReads live
          ([codeBuffer, codeLength, dataBuffer, dataLength] ++
            cutsets.1 ++ cutsets.2))
  | .codeBufferWrite address value, live =>
      (.codeBufferWrite address value, wordDeadAddReads live [address, value])
  | .dataBufferWrite address value, live =>
      (.dataBufferWrite address value, wordDeadAddReads live [address, value])
  | .ffi function configuration configurationLength array arrayLength liveSet, live =>
      (.ffi function configuration configurationLength array arrayLength liveSet,
        wordDeadAddReads live
          ([configuration, configurationLength, array, arrayLength] ++
            liveSet.1 ++ liveSet.2))
  | .shareInst operator name address, live =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          /- Cake deliberately retains ShareInst loads: even a dead load
             emits the observable shared-memory event used by the FFI model. -/
          (.shareInst operator name address,
            wordDeadAddReads (wordDeadRemoveWrites live [name])
              (wordExpReadVars address))
      | .store | .store8 | .store16 | .store32 =>
          (.shareInst operator name address,
            wordDeadAddReads live
              ([name] ++ wordExpReadVars address))
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordRemoveDeadProgram (program : WordProg α) : WordProg α :=
  (wordDeadCode program []).1

end Flapjack.RiscV

namespace Flapjack.RiscV.CakeRegAlloc

open Flapjack
open Flapjack.RiscV

/-! The source-shaped allocator boundary: full SSA is performed first, then
Cake's dead-program pass feeds the clash tree and IRC allocator. -/
def cakeAllocateWordFunctionAfterDead (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg α) :
    Option (WordSsaState × List Nat × WordProg α × WordSpillState) :=
  let (state, renamedParameters, ssaProgram) :=
    wordFullSsaCcTrans parameters.length program
  let ssaProgram := wordRemoveDeadProgram ssaProgram
  let tree := wordClashTree ssaProgram []
  let fs := cakeGetStackOnly ssaProgram
  let forced := cakeGetForced ssaProgram
  let (wordMoves, spillCosts) := wordGetHeuristics 3 currentFunction ssaProgram
  let moves := wordMoves.map (fun move => (move.priority, (move.left, move.right)))
  let bij := cakeMkBij tree
  let scost := spillCosts.map (fun costs =>
    costs.filterMap (fun entry =>
      (lookupNatInfo entry.1 bij.toAllocator).map
        (fun node => (node, entry.2))))
  match cakeDoRegAlloc .irc scost (wordAllocatableRegisters.length + 2)
      moves tree forced fs with
  | none => none
  | some colouring =>
      some (state, renamedParameters, ssaProgram,
        cakeColourWordSpillState (wordAllocatableRegisters.length + 2)
          parameters ssaProgram colouring)

end Flapjack.RiscV.CakeRegAlloc
