import Flapjack.Compiler.Backend.WordToStack.Proofs.MoveAuxStep
import Flapjack.Compiler.Backend.Parmove.SeqsemUnchanged

namespace Flapjack.WordToStackProofs.MoveAuxReconstruction
open Flapjack.Compiler.Backend.Parmove

/-- HOL inhabitedness for its existing option THE. All head values observed
here are established SOME; no new default or total list accessor is defined. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Flapjack list grouping of the original reversed real scheduled destinations.
No separate HOL declaration names this grouping. -/
def destinations (moves : List (Option Nat × Option Nat)) : List (Option Nat) :=
  ((moves.reverse).map Prod.fst).filter Option.isSome

/-- Flapjack grouping of the original complete source post-state expression.
This is an algebraic state expression, not a replacement source evaluator or
an assumed state relation; the full native theorem proves it is related. -/
noncomputable def sourcePost {width : Nat} [NeZero width] {C F : Type}
    (moves : List (Option Nat × Option Nat)) (env : Option Nat → Option (WordLocW width))
    (state : WordSemStateFiniteExact width C F) : WordSemStateFiniteExact width C F :=
  WordSemStateFiniteExact.setVars
    ((destinations moves).map (fun x => 2*holThe x))
    ((destinations moves).map (fun x => holThe (seqsem moves env x))) state

/-- Flapjack inline native paired insertion append identity for same-position
maps. Both key and value lists have the same length by construction. -/
private theorem insertMapsLast {α β : Type} (xs : List α) (key : α → Nat) (value : α → β)
    (lastKey : Nat) (lastValue : β) (tree : Spt β) :
    LoopSemStateFiniteExact.sptAlistInsert (xs.map key ++ [lastKey])
      (xs.map value ++ [lastValue]) tree =
    LoopSemStateFiniteExact.sptAlistInsert (xs.map key) (xs.map value)
      (sptInsert lastKey lastValue tree) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.cons_append,LoopSemStateFiniteExact.sptAlistInsert,ih]

/-- Flapjack inline full source-state equality from original3246–3285. It
retains the actual successful head value and original distinct real scheduled
 destinations. Final head value is derived by seqsem_move_unchanged; every
source-state field and the entire native local tree is preserved. -/
theorem sourceStateReconstruction {width : Nat} [NeZero width] {C F : Type}
    (destination source : Option Nat) (moves : List (Option Nat × Option Nat))
    (env : Option Nat → Option (WordLocW width)) (state : WordSemStateFiniteExact width C F)
    (value : WordLocW width) (read : env source=some value)
    (distinct : (((destination,source)::moves).map Prod.fst |>.filter Option.isSome).Nodup) :
    sourcePost moves (updateEnv env destination (env source))
      (match destination with | none => state | some y => WordSemStateFiniteExact.setVar (2*y) value state) =
    sourcePost ((destination,source)::moves) env state := by
  cases destination with
  | none =>
    simp [sourcePost,destinations,List.reverse_cons,List.map_append,List.filter_append,seqsem]
  | some y =>
    have absent : some y ∉ moves.map Prod.fst := by
      have parts : some y ∉ (moves.map Prod.fst).filter Option.isSome ∧
          ((moves.map Prod.fst).filter Option.isSome).Nodup := by simpa using distinct
      have fresh := parts.1
      simpa using fresh
    have unchanged := seqsemMoveUnchanged moves (updateEnv env (some y) (env source)) (some y) absent
    have headValue : seqsem moves (updateEnv env (some y) (env source)) (some y)=some value := by
      simpa [updateEnv,read] using unchanged
    simp only [sourcePost,destinations,List.reverse_cons,List.map_append,
      List.filter_append,List.filter_cons,Option.isSome_some,↓reduceIte,List.filter_nil,
      List.map_append,List.map_cons,List.map_nil,seqsem,headValue,holThe]
    unfold WordSemStateFiniteExact.setVars WordSemStateFiniteExact.setVar
    rw [insertMapsLast]

end Flapjack.WordToStackProofs.MoveAuxReconstruction
