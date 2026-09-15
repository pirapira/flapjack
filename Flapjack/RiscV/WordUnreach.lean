import Flapjack.RiscV.WordDeadCode

/-!
# Cake-shaped unreachable-sequence cleanup

This is the small `word_unreach` boundary from Cake's
`word_unreachScript.sml`: right-associate sequences, discard continuations
after unconditional transfers, and merge adjacent parallel moves.  It runs
after the SSA dead pass and before allocation, where move merging affects the
allocator's preference graph without changing the observable Word program.
-/

namespace Flapjack.RiscV

open Flapjack

def wordUnreachLookup (moves : List (Nat × Nat)) (name : Nat) : Nat :=
  (lookupNatInfo name moves).getD name

def wordUnreachAnub : List (Nat × Nat) → List Nat → List (Nat × Nat)
  | [], _ => []
  | (destination, source) :: moves, seen =>
      if destination ∈ seen then
        wordUnreachAnub moves seen
      else
        (destination, source) :: wordUnreachAnub moves (destination :: seen)
termination_by moves _ => sizeOf moves
decreasing_by all_goals decreasing_trivial

def wordUnreachMergeMoves (first second : List (Nat × Nat)) : List (Nat × Nat) :=
  let rewritten := second.map (fun move =>
    (move.1, wordUnreachLookup first move.2))
  wordUnreachAnub (rewritten ++ first) []

def wordUnreachSimpSeq (first second : WordProg α) : WordProg α :=
  match first with
  | .skip => second
  | .raise _ | .return _ _ | .break _ | .continue _ => first
  | .call none _ _ _ => first
  | .move firstPriority firstMoves =>
      match second with
      | .skip => first
      | .move secondPriority secondMoves =>
          .move (max firstPriority secondPriority)
            (wordUnreachMergeMoves firstMoves secondMoves)
      | .seq (.move secondPriority secondMoves) rest =>
          let merged := .move (max firstPriority secondPriority)
            (wordUnreachMergeMoves firstMoves secondMoves)
          match rest with
          | .skip => merged
          | _ => .seq merged rest
      | _ => .seq first second
  | _ =>
      match second with
      | .skip => first
      | _ => .seq first second

def wordRemoveUnreachable : WordProg α → WordProg α
  | .seq first second =>
      wordUnreachSimpSeq (wordRemoveUnreachable first)
        (wordRemoveUnreachable second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right
        (wordRemoveUnreachable thenBranch)
        (wordRemoveUnreachable elseBranch)
  | .loop liveIn body liveOut =>
      .loop liveIn (wordRemoveUnreachable body) liveOut
  | .mustTerminate body => .mustTerminate (wordRemoveUnreachable body)
  | .call returns target arguments none =>
      .call returns target arguments none
  | .call returns target arguments
      (some (exception, handlerBody, handlerLabel, handlerEntryLabel)) =>
      .call returns target arguments
        (some (exception, wordRemoveUnreachable handlerBody,
          handlerLabel, handlerEntryLabel))
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

end Flapjack.RiscV
