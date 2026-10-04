import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.ConstFp
import Flapjack.Pancake.Proofs.WordConvs.WordSimpLabels.HoistPrerequisites

namespace Flapjack.WordConvs.WordSimpLabels
open Flapjack Flapjack.Compiler.Backend.WordSimp

/-- Native strategy observation after actual sequential map threading.
This Flapjack-only projection lemma exposes the original dummy strategy. -/
private theorem dummyAfterPrefix {width : Nat} [NeZero width]
    (branch interm dummy : WordLangProgHOL (BitVec width)) :
    destRaiseNum (destSeq (constFp (.seq (.seq branch interm) dummy))).2 =
      destRaiseNum (constFpLoop dummy
        (constFpLoop interm (constFpLoop branch .ln).2).2).1 := by
  simp [constFp, constFpLoopSeq, destSeq]

/-- Simple programs contribute no labels; Flapjack-only structural support. -/
private theorem simpleLabelsEmpty {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (simple : isSimple program = true) :
    extractLabels program = [] := by
  cases program <;> simp_all [isSimple, extractLabels]

/-- Actual dummy tags select the same arbitrary conditional branch. This
Flapjack-only consequence retains the reviewed native strategy operation. -/
private theorem dummySelectBranch {width : Nat} [NeZero width]
    (cmp : Cmp) (lhs : Nat) (rhs : WordRegImm (BitVec width)) (cs : Spt (BitVec width)) :
    (destRaiseNum (constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) cs).1 = 1 →
      ∀ first second, constFpLoop (.ite cmp lhs rhs first second) cs = constFpLoop first cs) ∧
    (destRaiseNum (constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) cs).1 = 2 →
      ∀ first second, constFpLoop (.ite cmp lhs rhs first second) cs = constFpLoop second cs) := by
  have strategy := constFpLoopDummyCases cmp lhs rhs cs
    (constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) cs).2
    (constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) cs).1 rfl
  constructor
  · intro selected
    rcases strategy with one | two | zero
    · exact one.2
    · omega
    · omega
  · intro selected
    rcases strategy with one | two | zero
    · omega
    · exact two.2
    · omega

/-- Actual folded dummy results have precisely the original three numeric
possibilities. No target-strategy fact is assumed. -/
private theorem dummyTagCases {width : Nat} [NeZero width]
    (cmp : Cmp) (lhs : Nat) (rhs : WordRegImm (BitVec width)) (cs : Spt (BitVec width)) :
    let tag := destRaiseNum (constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) cs).1
    tag = 0 ∨ tag = 1 ∨ tag = 2 := by
  have strategy := constFpLoopDummyCases cmp lhs rhs cs
    (constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) cs).2
    (constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) cs).1 rfl
  rcases strategy with one | two | zero
  · exact Or.inr (Or.inl one.1)
  · exact Or.inr (Or.inr two.1)
  · exact Or.inl zero

/-- Flapjack-only containment/distinctness facts for an original branch list. -/
private theorem labelsRelLeft {β : Type} (a b : List β) : labelsRel (a ++ b) a :=
  ⟨fun h => (List.nodup_append.mp h).1, fun _ h => List.mem_append.mpr (Or.inl h)⟩

private theorem labelsRelRight {β : Type} (a b : List β) : labelsRel (a ++ b) b :=
  ⟨fun h => (List.nodup_append.mp h).2.1, fun _ h => List.mem_append.mpr (Or.inr h)⟩

/-- Flapjack-only empty-list consequence of both original relation clauses. -/
private theorem relatedNil {β : Type} (a : List β) (related : labelsRel [] a) : a = [] := by
  cases a with
  | nil => rfl
  | cons x xs => exact False.elim (by simpa using related.2 x (by simp))

/-- One actual native conditional step consumes either one or both already
folded branches; this is internal proof factoring, not another HOL port. -/
private theorem foldedIfLabels {width : Nat} [NeZero width]
    (op : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width)) :
    labelsRel (extractLabels (constFpLoop a cs).1 ++ extractLabels (constFpLoop b cs).1)
      (extractLabels (constFpLoop (.ite op r ri a b) cs).1) := by
  rw [constFpLoop]
  split
  · split
    · exact labelsRelLeft _ _
    · exact labelsRelRight _ _
  · simpa only [extractLabels] using
      labelsRel_refl (extractLabels (constFpLoop a cs).1 ++ extractLabels (constFpLoop b cs).1)

/-- Actual sequential map threading followed by a proved selected branch.
No label property of the result is assumed; every component comes from the
full original constant-folding theorem. Flapjack-only factoring lemma. -/
private theorem prefixSelectedLabels {width : Nat} [NeZero width]
    (a interm continuation selected : WordLangProgHOL (BitVec width))
    (empty : extractLabels interm = [])
    (selection : constFpLoop continuation (constFpLoop interm (constFpLoop a .ln).2).2 =
      constFpLoop selected (constFpLoop interm (constFpLoop a .ln).2).2) :
    labelsRel (extractLabels a ++ extractLabels selected)
      (extractLabels (constFp (.seq (.seq a interm) continuation))) := by
  have aRel := extractLabelsConstFpLoop a .ln (constFpLoop a .ln).1 (constFpLoop a .ln).2 rfl
  have iRel := extractLabelsConstFpLoop interm (constFpLoop a .ln).2
    (constFpLoop interm (constFpLoop a .ln).2).1
    (constFpLoop interm (constFpLoop a .ln).2).2 rfl
  rw [empty] at iRel
  have iEmpty := relatedNil _ iRel
  have sRel := extractLabelsConstFpLoop selected (constFpLoop interm (constFpLoop a .ln).2).2
    (constFpLoop selected (constFpLoop interm (constFpLoop a .ln).2).2).1
    (constFpLoop selected (constFpLoop interm (constFpLoop a .ln).2).2).2 rfl
  simpa only [constFp, constFpLoopSeq, selection, extractLabels, iEmpty, List.append_nil] using
    labelsRel_append aRel sRel

/-- Flapjack-only exact rearrangement of the original four label blocks. -/
private theorem shuffleLabels {β : Type} (a b x y : List β) :
    labelsRel ((a ++ b) ++ (x ++ y)) ((a ++ x) ++ (b ++ y)) := by
  have middle : (x ++ b).Perm (b ++ x) := List.perm_append_comm
  simpa only [List.append_assoc] using labelsRel_of_perm ((middle.append_left a).append_right y)

/-- Successful original dummy observations select complementary branches;
this establishes the entire actual output relation internally. -/
private theorem successfulHoistLabels {width : Nat} [NeZero width]
    (op cmp : Cmp) (r lhs : Nat) (ri rhs : WordRegImm (BitVec width))
    (a b interm x y : WordLangProgHOL (BitVec width))
    (empty : extractLabels interm = [])
    (_nonzero : destRaiseNum (destSeq (constFp (.seq (.seq a interm)
      (.ite cmp lhs rhs (.raise 1) (.raise 2))))).2 ≠ 0)
    (sum : destRaiseNum (destSeq (constFp (.seq (.seq a interm)
      (.ite cmp lhs rhs (.raise 1) (.raise 2))))).2 +
      destRaiseNum (destSeq (constFp (.seq (.seq b interm)
      (.ite cmp lhs rhs (.raise 1) (.raise 2))))).2 = 3) :
    labelsRel ((extractLabels a ++ extractLabels b) ++ (extractLabels x ++ extractLabels y))
      (extractLabels (constFp (.ite op r ri
        (.seq (.seq a interm) (.ite cmp lhs rhs x y))
        (.seq (.seq b interm) (.ite cmp lhs rhs x y))))) := by
  rw [dummyAfterPrefix] at _nonzero
  rw [dummyAfterPrefix, dummyAfterPrefix] at sum
  let csA := (constFpLoop interm (constFpLoop a .ln).2).2
  let csB := (constFpLoop interm (constFpLoop b .ln).2).2
  have casesA := dummyTagCases cmp lhs rhs csA
  have casesB := dummyTagCases cmp lhs rhs csB
  have complementary :
      (destRaiseNum (constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) csA).1 = 1 ∧
       destRaiseNum (constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) csB).1 = 2) ∨
      (destRaiseNum (constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) csA).1 = 2 ∧
       destRaiseNum (constFpLoop (.ite cmp lhs rhs (.raise 1) (.raise 2)) csB).1 = 1) := by
    dsimp only [csA, csB] at casesA casesB ⊢
    omega
  rcases complementary with ⟨one, two⟩ | ⟨two, one⟩
  · have aRel := prefixSelectedLabels a interm (.ite cmp lhs rhs x y) x empty
      ((dummySelectBranch cmp lhs rhs csA).1 one x y)
    have bRel := prefixSelectedLabels b interm (.ite cmp lhs rhs x y) y empty
      ((dummySelectBranch cmp lhs rhs csB).2 two x y)
    have combined := labelsRel_trans (shuffleLabels (extractLabels a) (extractLabels b)
      (extractLabels x) (extractLabels y)) (labelsRel_append aRel bRel)
    exact labelsRel_trans combined (foldedIfLabels op r ri _ _ .ln)
  · have aRel := prefixSelectedLabels a interm (.ite cmp lhs rhs x y) y empty
      ((dummySelectBranch cmp lhs rhs csA).2 two x y)
    have bRel := prefixSelectedLabels b interm (.ite cmp lhs rhs x y) x empty
      ((dummySelectBranch cmp lhs rhs csB).1 one x y)
    have reordered := labelsRel_append (labelsRel_refl (extractLabels a ++ extractLabels b))
      (labelsRelAppendImp (extractLabels x) (extractLabels y) (extractLabels y ++ extractLabels x)
        (labelsRel_refl (extractLabels y ++ extractLabels x)))
    have combined := labelsRel_trans reordered
      (labelsRel_trans (shuffleLabels (extractLabels a) (extractLabels b)
        (extractLabels y) (extractLabels x)) (labelsRel_append aRel bRel))
    exact labelsRel_trans combined (foldedIfLabels op r ri _ _ .ln)

/-- Full original hoist2 label relation. The unused HOL binder s is vacuous in
both guards and conclusion and is omitted. All real count, compiler-output,
destructor, dummy-program and empty-intermediate-label guards are retained. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "labels_rel_hoist2"
  (words_as_type_indexed_bitvec)]
theorem labelsRelHoist2 {width : Nat} [NeZero width]
    (count : Nat) (first interm dummy second out : WordLangProgHOL (BitVec width))
    (cmp : Cmp) (lhs : Nat) (rhs : WordRegImm (BitVec width))
    (branch1 branch2 : WordLangProgHOL (BitVec width))
    (hoisted : tryIfHoist2 count first interm dummy second = some out)
    (dest : destIf second = some (cmp,lhs,rhs,branch1,branch2))
    (dummyEq : dummy = .ite cmp lhs rhs (.raise 1) (.raise 2))
    (intermLabels : extractLabels interm = []) :
    labelsRel (extractLabels first ++ extractLabels second) (extractLabels out) := by
  subst dummy
  rw [(destIfIff second cmp lhs rhs branch1 branch2).mp dest] at *
  clear dest
  induction count generalizing first interm out with
  | zero => simp [tryIfHoist2] at hoisted
  | succ count ih =>
    cases first <;> simp only [tryIfHoist2, reduceCtorEq] at hoisted
    case seq first next =>
      split at hoisted
      · rename_i otherCmp otherLhs otherRhs a b destNext
        split at hoisted
        · contradiction
        · split at hoisted
          · contradiction
          · simp only [Option.some.injEq] at hoisted
            rw [← hoisted, (destIfIff next otherCmp otherLhs otherRhs a b).mp destNext]
            simpa only [extractLabels, List.append_assoc] using
              labelsRel_append (labelsRel_refl (extractLabels first))
                (successfulHoistLabels otherCmp cmp otherLhs lhs otherRhs rhs
                  a b interm branch1 branch2 intermLabels (by assumption) (by omega))
      · split at hoisted
        · rename_i simple
          have nextLabels := simpleLabelsEmpty next simple
          have prefixLabels : extractLabels (.seq next interm) = [] := by
            simp [extractLabels, nextLabels, intermLabels]
          simpa [extractLabels, nextLabels] using ih first (.seq next interm) out prefixLabels hoisted
        · contradiction
    case ite op r ri a b =>
      split at hoisted
      · contradiction
      · split at hoisted
        · contradiction
        · simp only [Option.some.injEq] at hoisted
          rw [← hoisted]
          simpa only [extractLabels, List.append_assoc] using
            successfulHoistLabels op cmp r lhs ri rhs a b interm branch1 branch2
              intermLabels (by assumption) (by omega)


/-- Flapjack-only wrapper consequence: the actual hoist1 output has the
relation established by the complete original hoist2 theorem. -/
private theorem hoist1Labels {width : Nat} [NeZero width]
    (first second out : WordLangProgHOL (BitVec width))
    (run : tryIfHoist1 first second = some out) :
    labelsRel (extractLabels first ++ extractLabels second) (extractLabels out) := by
  unfold tryIfHoist1 at run
  split at run
  · contradiction
  · rename_i cmp lhs rhs a b dest
    exact labelsRelHoist2 rewriteDuplicateIfMaxReassoc first .skip
      (.ite cmp lhs rhs (.raise 1) (.raise 2)) second out cmp lhs rhs a b run dest rfl rfl

/-- Full original duplicate-if traversal label relation, including every call
return and exception-handler family. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "labels_rel_simp_duplicate_if"
  (words_as_type_indexed_bitvec)]
theorem labelsRelSimpDuplicateIf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    labelsRel (extractLabels program) (extractLabels (simpDuplicateIf program)) := by
  fun_induction simpDuplicateIf program <;> try simp_all only [extractLabels]
  all_goals try first
    | exact labelsRel_refl _
    | solve | apply labelsRel_append <;> assumption
  case case2 ret dest args handler ihRet ihHandler =>
    cases ret with
    | none => simp only [extractLabels]; exact labelsRel_refl _
    | some ret =>
      rcases ret with ⟨ns, cuts, q, l1, l2⟩
      cases handler with
      | none =>
        simp only [extractLabels] at *
        exact labelsRel_cons (labelsRel_refl _) ihRet
      | some handler =>
        rcases handler with ⟨n, body, h1, h2⟩
        simp only [extractLabels] at *
        exact labelsRel_cons (labelsRel_refl _)
          (labelsRel_cons (labelsRel_refl _) (labelsRel_append ihRet ihHandler))
  case case5 =>
    rename_i p1 p2 p1x p2x p3 run ihA ihB
    rw [extractLabelsSeqAssoc]
    exact labelsRel_trans (labelsRel_append ihA ihB) (hoist1Labels p1x p2x p3 run)


end Flapjack.WordConvs.WordSimpLabels
