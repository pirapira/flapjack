import Flapjack.RiscV.CakeRegAlloc
import Flapjack.RiscV.WordCse
import Flapjack.RiscV.WordCopyProp

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

/-! Cake's `remove_dead (Move pri ls)` keeps the priority of the surviving
    moves.  The priority orders the coalescing worklist (`sort_moves` sorts
    descending and `do_coalesce` consumes the first compatible move), so the
    `Move1` SSA entry/ABI shuffle must stay priority 1 for the parameters to
    coalesce onto the ABI registers. -/
def wordDeadMove (priority : Nat) (live : List Nat) (moves : List (Nat × Nat)) :
    WordProg α × List Nat :=
  let kept := moves.filter (fun move => move.1 ∈ live)
  if kept.isEmpty then
    (.skip, live)
  else
    (.move priority kept,
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

def wordDeadCodeAux : WordProg α → List Nat → List (List Nat × List Nat) →
    WordProg α × List Nat
  | .skip, live, _ => (.skip, live)
  | .move priority moves, live, _ => wordDeadMove priority live moves
  | .assign destination value, live, _ =>
      if destination ∈ live then
        (.assign destination value,
          wordDeadAddReads (wordDeadRemoveWrites live [destination])
            (wordExpReadVars value))
      else
        (.skip, live)
  | .inst instruction, live, _ => wordDeadInst live instruction
  | .get destination store, live, _ =>
      if destination ∈ live then
        (.get destination store,
          wordDeadAddReads (wordDeadRemoveWrites live [destination]) [])
      else
        (.skip, live)
  | .store address value, live, _ =>
      (.store address value,
        wordDeadAddReads live (wordExpReadVars address ++ [value]))
  | .set store value, live, _ =>
      (.set store value, wordDeadAddReads live (wordExpReadVars value))
  | .seq first second, live, frames =>
      let (second', live) := wordDeadCodeAux second live frames
      let (first', live) := wordDeadCodeAux first live frames
      (match first', second' with
       | .skip, program => program
       | program, .skip => program
       | _, _ => .seq first' second', live)
  | .ite operator condition right thenBranch elseBranch, live, frames =>
      let (then', thenLive) := wordDeadCodeAux thenBranch live frames
      let (else', elseLive) := wordDeadCodeAux elseBranch live frames
      let rightReads := match right with
        | .imm _ => []
        | .reg name => [name]
      (.ite operator condition right then' else',
        wordDeadAddReads (thenLive ++ elseLive) (condition :: rightReads))
  | .loop liveIn body liveOut, _live, frames =>
      let (body', _) := wordDeadCodeAux body liveIn ((liveIn, liveOut) :: frames)
      (.loop liveIn body' liveOut, liveIn)
  | .mustTerminate body, live, frames =>
      let (body', live) := wordDeadCodeAux body live frames
      (.mustTerminate body', live)
  | .break label, _live, frames =>
      (.break label, (wordClashTreeFindLoopFrame label frames).map Prod.snd |>.getD [])
  | .continue label, _live, frames =>
      (.continue label, (wordClashTreeFindLoopFrame label frames).map Prod.fst |>.getD [])
  | .raise exception, live, _ => (.raise exception, exception :: live)
  | .return label values, live, _ =>
      (.return label values, wordDeadAddReads (label :: live) values)
  | .tick, live, _ => (.tick, live)
  | .locValue destination source, live, _ =>
      if destination ∈ live then
        (.locValue destination source,
          wordDeadAddReads (wordDeadRemoveWrites live [destination]) [])
      else
        (.skip, live)
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments handler, live, frames =>
      let (returnCode', _) := wordDeadCodeAux returnCode live frames
      let handler' := match handler with
        | none => none
        | some (exception, body, handlerLabel, handlerEntryLabel) =>
            some (exception, (wordDeadCodeAux body live frames).1,
              handlerLabel, handlerEntryLabel)
      (.call (some (destinations, cutsets, returnCode', returnLabel, entryLabel))
          target arguments handler',
        wordDeadAddReads live (wordProgReadVars
          (.call (some (destinations, cutsets, returnCode', returnLabel, entryLabel))
            target arguments handler')))
  | .call returns target arguments handler, live, _ =>
      (.call returns target arguments handler,
        wordDeadAddReads live (wordProgReadVars
          (.call returns target arguments handler)))
  | .alloc destination cutsets, live, _ =>
      (.alloc destination cutsets,
        wordDeadAddReads (wordDeadRemoveWrites live [destination])
          (cutsets.1 ++ cutsets.2))
  | .storeConsts source bitmap codeLength dataLength constants, live, _ =>
      (.storeConsts source bitmap codeLength dataLength constants,
        wordDeadAddReads live [source, bitmap, codeLength, dataLength])
  | .opCurrHeap operator destination source, live, _ =>
      (.opCurrHeap operator destination source,
        wordDeadAddReads (wordDeadRemoveWrites live [destination]) [source])
  | .install codeBuffer codeLength dataBuffer dataLength cutsets, live, _ =>
      (.install codeBuffer codeLength dataBuffer dataLength cutsets,
        wordDeadAddReads live
          ([codeBuffer, codeLength, dataBuffer, dataLength] ++
            cutsets.1 ++ cutsets.2))
  | .codeBufferWrite address value, live, _ =>
      (.codeBufferWrite address value, wordDeadAddReads live [address, value])
  | .dataBufferWrite address value, live, _ =>
      (.dataBufferWrite address value, wordDeadAddReads live [address, value])
  | .ffi function configuration configurationLength array arrayLength liveSet, live, _ =>
      (.ffi function configuration configurationLength array arrayLength liveSet,
        wordDeadAddReads live
          ([configuration, configurationLength, array, arrayLength] ++
            liveSet.1 ++ liveSet.2))
  | .shareInst operator name address, live, _ =>
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
decreasing_by
  all_goals simp_wf
  all_goals omega

def wordDeadCode : WordProg α → List Nat → WordProg α × List Nat
  | program, live => wordDeadCodeAux program live []

def wordRemoveDeadProgram (program : WordProg α) : WordProg α :=
  (wordDeadCode program []).1

/-! Cake's two-register arithmetic pass turns a selected binary operation into
    a destination/source move followed by an in-place operation.  The Word
    carrier keeps the selected arithmetic as an assignment, so preserve that
    move preference at the same post-copy boundary. -/
def wordThreeToTwoReg : WordProg α → WordProg α
  | .assign destination (.op operator [.var left, .const value]) =>
      .seq (.move 0 [(destination, left)])
        (.assign destination (.op operator [.var destination, .const value]))
  | .assign destination (.op operator [.var left, .var right]) =>
      .seq (.move 0 [(destination, left)])
        (.assign destination (.op operator [.var destination, .var right]))
  | .seq first second =>
      .seq (wordThreeToTwoReg first) (wordThreeToTwoReg second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right (wordThreeToTwoReg thenBranch)
        (wordThreeToTwoReg elseBranch)
  | .loop liveIn body liveOut =>
      .loop liveIn (wordThreeToTwoReg body) liveOut
  | .mustTerminate body => .mustTerminate (wordThreeToTwoReg body)
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments none =>
      .call (some (destinations, cutsets,
        wordThreeToTwoReg returnCode, returnLabel, entryLabel))
        target arguments none
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments (some (exception, body, handlerLabel, handlerEntryLabel)) =>
      .call (some (destinations, cutsets,
        wordThreeToTwoReg returnCode, returnLabel, entryLabel))
        target arguments
        (some (exception, wordThreeToTwoReg body,
          handlerLabel, handlerEntryLabel))
  | .call none target arguments none =>
      .call none target arguments none
  | .call none target arguments (some (exception, body, handlerLabel, handlerEntryLabel)) =>
      .call none target arguments
        (some (exception, wordThreeToTwoReg body,
          handlerLabel, handlerEntryLabel))
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! The post-copy `word_unreach` boundary.  The public WordUnreach module
    depends on this file for its dead-code definitions, so keep this small
    local copy here to preserve the allocator pass order without introducing
    an import cycle. -/
def wordCopyUnreachMergeMoves (first second : List (Nat × Nat)) :
    List (Nat × Nat) :=
  let rewritten := second.map (fun move =>
    (move.1, (lookupNatInfo move.2 first).getD move.2))
  (rewritten ++ first).foldl (fun seen move =>
    if seen.any (fun prior => prior.1 == move.1) then seen
    else seen ++ [move]) []

def wordCopyUnreachSeq (first second : WordProg α) : WordProg α :=
  match first, second with
  | .skip, program => program
  | .raise _, _ => first
  | .return _ _, _ => first
  | .break _, _ => first
  | .continue _, _ => first
  | .call none _ _ _, _ => first
  | .move firstPriority firstMoves, .skip =>
      .move firstPriority firstMoves
  | .move firstPriority firstMoves, .move secondPriority secondMoves =>
      .move (max firstPriority secondPriority)
        (wordCopyUnreachMergeMoves firstMoves secondMoves)
  | .move firstPriority firstMoves,
      .seq (.move secondPriority secondMoves) rest =>
      let merged := .move (max firstPriority secondPriority)
        (wordCopyUnreachMergeMoves firstMoves secondMoves)
      match rest with
      | .skip => merged
      | _ => .seq merged rest
  | _, .skip => first
  | _, _ => .seq first second

/-! `Seq_assoc_right` first flattens every sequence, including sequences
    nested in call continuations.  Keeping the parts as a list makes that
    association explicit and lets `wordCopyUnreachSeq` merge adjacent moves
    after copy propagation, just as Cake's `dest_Seq_Move` does. -/
def wordCopyUnreachParts : WordProg α → List (WordProg α)
  | .seq first second => wordCopyUnreachParts first ++ wordCopyUnreachParts second
  | .ite operator condition right thenBranch elseBranch =>
      [.ite operator condition right
        (wordCopyUnreachParts thenBranch |>.foldr wordCopyUnreachSeq .skip)
        (wordCopyUnreachParts elseBranch |>.foldr wordCopyUnreachSeq .skip)]
  | .loop liveIn body liveOut =>
      [.loop liveIn (wordCopyUnreachParts body |>.foldr wordCopyUnreachSeq .skip) liveOut]
  | .mustTerminate body =>
      [.mustTerminate (wordCopyUnreachParts body |>.foldr wordCopyUnreachSeq .skip)]
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments handler =>
      let handler' := match handler with
        | none => none
        | some (exception, body, handlerLabel, handlerEntryLabel) =>
            some (exception,
              wordCopyUnreachParts body |>.foldr wordCopyUnreachSeq .skip,
              handlerLabel, handlerEntryLabel)
      [.call (some (destinations, cutsets,
          wordCopyUnreachParts returnCode |>.foldr wordCopyUnreachSeq .skip,
          returnLabel, entryLabel)) target arguments handler']
  | program => [program]
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordRemoveUnreachableAfterCopy (program : WordProg α) : WordProg α :=
  wordCopyUnreachParts program |>.foldr wordCopyUnreachSeq .skip

end Flapjack.RiscV

namespace Flapjack.RiscV.CakeRegAlloc

open Flapjack
open Flapjack.RiscV

/-! The source-shaped allocator boundary: full SSA is performed first, then
Cake's dead-program pass feeds the clash tree and IRC allocator. -/
def cakeAllocateWordFunctionAfterDead [OfNat α 0] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg α) [BEq α] :
    Option (WordSsaState × List Nat × WordProg α × WordSpillState) :=
  let (state, renamedParameters, ssaProgram) :=
    wordFullSsaCcTrans parameters.length program
  let ssaProgram := wordRemoveDeadProgram ssaProgram
  let ssaProgram := wordCseProp ssaProgram
  let ssaProgram := wordCopyProp ssaProgram
  let ssaProgram := wordThreeToTwoReg ssaProgram
  let ssaProgram := wordRemoveUnreachableAfterCopy ssaProgram
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
  match cakeDoRegAlloc .irc scost cakeRiscVRegisterCount
      moves tree forced fs with
  | none => none
  | some colouring =>
      some (state, renamedParameters, ssaProgram,
        cakeColourWordSpillState cakeRiscVRegisterCount
          parameters ssaProgram colouring)

end Flapjack.RiscV.CakeRegAlloc
