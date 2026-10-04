import Flapjack.Compiler.Backend.WordSimp
import Flapjack.Pancake.WordConvs

namespace Flapjack.WordConvs
open Flapjack.Compiler.Backend.WordSimp

/-- Original local Seq equation selected from the native constant-folding definition. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "const_fp_loop_Seq"
  (words_as_type_indexed_bitvec)]
theorem constFpLoopSeq {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width)) :
    constFpLoop (.seq first second) cs =
      let (firstPost, csPost) := constFpLoop first cs
      let (secondPost, csPostPost) := constFpLoop second csPost
      (.seq firstPost secondPost, csPostPost) := by
  rw [constFpLoop]

/-- Original full conditional destructor equivalence. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "dest_If_thm"
  (words_as_type_indexed_bitvec)]
theorem destIfIff {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (cmp : Cmp) (lhs : Nat)
    (rhs : WordRegImm (BitVec width)) (first second : WordLangProgHOL (BitVec width)) :
    destIf program = some (cmp, lhs, rhs, first, second) ↔
      program = .ite cmp lhs rhs first second := by
  cases program <;> simp [destIf]

/-- Full original dummy strategy disjunction, including its universal arbitrary
branch equations. It proves the strategy from the actual map lookups. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "const_fp_loop_dummy_cases"
  (words_as_type_indexed_bitvec)]
theorem constFpLoopDummyCases {width : Nat} [NeZero width]
    (cmp : Cmp) (lhs : Nat) (rhs : WordRegImm (BitVec width))
    (cs csPost : Spt (BitVec width)) (programPost : WordLangProgHOL (BitVec width))
    (compiled : constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) cs =
      (programPost, csPost)) :
    (destRaiseNum programPost = 1 ∧
      ∀ first second, constFpLoop (.ite cmp lhs rhs first second) cs = constFpLoop first cs) ∨
    (destRaiseNum programPost = 2 ∧
      ∀ first second, constFpLoop (.ite cmp lhs rhs first second) cs = constFpLoop second cs) ∨
    destRaiseNum programPost = 0 := by
  simp only [constFpLoop] at compiled
  split at compiled
  · split at compiled
    · simp only [Prod.mk.injEq] at compiled
      rcases compiled with ⟨rfl, rfl⟩
      simp_all [constFpLoop, destRaiseNum]
    · simp only [Prod.mk.injEq] at compiled
      rcases compiled with ⟨rfl, rfl⟩
      simp_all [constFpLoop, destRaiseNum]
  · simp only [Prod.mk.injEq] at compiled
    rcases compiled with ⟨rfl, rfl⟩
    simp_all [constFpLoop, destRaiseNum]

end Flapjack.WordConvs
