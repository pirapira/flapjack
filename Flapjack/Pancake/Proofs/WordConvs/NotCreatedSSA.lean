import Flapjack.Pancake.Proofs.WordConvs.SSAWfCutsets
import Flapjack.Pancake.WordConvs.NotCreated

/-!
# `wordConvsProof`: `not_created_subprogs` through SSA

The SSA group of `not_created_subprogs` preservation theorems of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml` (1128-1225). HOL's
free predicate `P` is the leading binder.
-/

namespace Flapjack.WordConvs

open Flapjack

section SSA

open Flapjack.Compiler.Backend.WordAlloc Flapjack.WordAlloc

variable {width : Nat} [NeZero width]

/-- HOL `ssa_cc_trans_inst_not_created_subprogs` (`wordConvsProofScript.sml:1128-1142`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ssa_cc_trans_inst_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_ssaCcTransInst {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (i : WordLangInst (BitVec width)) (ssa : Spt Nat) (na : Nat)
    (i' : WordLangProgHOL (BitVec width)) (ssa' : Spt Nat) (na' : Nat)
    (h : ssaCcTransInst i ssa na = (i', ssa', na')) : notCreatedSubprogsHOL P i' = true := by
  have : notCreatedSubprogsHOL P (ssaCcTransInst i ssa na).1 = true := by
    fun_cases ssaCcTransInst i ssa na <;> simp [notCreatedSubprogsHOL]
  rw [h] at this
  exact this

/-- HOL `fake_moves_not_created_subprogs` (`wordConvsProofScript.sml:1144-1157`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "fake_moves_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_fakeMoves {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool) (prio : Option (Unit ⊕ Unit))
    (ls : List Nat) (nL nR : Spt Nat) (n : Nat) (prog1 prog2 : WordLangProgHOL (BitVec width)) (n' : Nat)
    (ssa ssa' : Spt Nat) (h : fakeMoves prio ls nL nR n = (prog1, prog2, n', ssa, ssa')) :
    notCreatedSubprogsHOL P prog1 = true ∧ notCreatedSubprogsHOL P prog2 = true := by
  have all : ∀ (ls : List Nat) (l r : Spt Nat) (na : Nat),
      let (a, b, _, _, _) := fakeMoves (width := width) prio ls l r na
      notCreatedSubprogsHOL P a = true ∧ notCreatedSubprogsHOL P b = true := by
    intro ls
    induction ls with
    | nil => intro l r na; simp [fakeMoves, notCreatedSubprogsHOL]
    | cons x xs ih =>
        intro l r na
        generalize he : fakeMoves (width := width) prio xs l r na = result
        rcases result with ⟨a, b, count, treeL, treeR⟩
        have previous := ih l r na
        rw [he] at previous
        simp only [fakeMoves, he]
        cases hl : sptLookup x treeL <;> cases hr : sptLookup x treeR <;>
          simp_all [notCreatedSubprogsHOL, fakeMove]
  have result := all ls nL nR n
  rw [h] at result
  exact result

/-- HOL `fake_seq_not_created_subprogs` (`wordConvsProofScript.sml:1159-1163`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "fake_seq_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_fakeSeq {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool) :
    ∀ ls : List Nat, notCreatedSubprogsHOL P
      ((ls.map (fakeMove : Nat → WordLangProgHOL (BitVec width))).foldr .seq .skip) = true := by
  intro ls
  induction ls with
  | nil => simp [notCreatedSubprogsHOL]
  | cons name names ih => simpa [notCreatedSubprogsHOL, fakeMove] using ih

/-- HOL `loop_setup_not_created_subprogs` (`wordConvsProofScript.sml:1165-1174`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "loop_setup_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_loopSetup {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat)
    (setupProg : WordLangProgHOL (BitVec width)) (ssaRefreshed : Spt Nat) (naRefreshed : Nat)
    (setup : loopSetup names exitNames ssa na = (setupProg, ssaRefreshed, naRefreshed)) :
    notCreatedSubprogsHOL P setupProg = true := by
  unfold loopSetup at setup
  generalize hr : listNextVarRename
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isNone) ssa na = renamed at setup
  rcases renamed with ⟨fresh, extended, next⟩
  generalize hm : listNextVarRenameMove (width := width) extended next
    (((sptToAList (sptUnion names exitNames)).map Prod.fst).filter
      fun v => (sptLookup v ssa).isSome) = moved at setup
  rcases moved with ⟨moves, refreshed, nextOut⟩
  simp only [hr, hm] at setup
  have fake := notCreated_fakeSeq (width := width) P fresh
  have moveConvention : notCreatedSubprogsHOL P moves = true := by
    unfold listNextVarRenameMove at hm
    have projected := congrArg Prod.fst hm
    simp only at projected
    rw [← projected]
    simp [notCreatedSubprogsHOL]
  have output := congrArg Prod.fst setup
  simp only at output
  rw [← output]
  simp only [notCreatedSubprogsHOL, fake, moveConvention, Bool.and_self]

private theorem fixNotCreated (P : WordLangProgHOL (BitVec width) → Bool)
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    let out := fixInconsistencies (width := width) prio l r next
    notCreatedSubprogsHOL P out.1 = true ∧ notCreatedSubprogsHOL P out.2.1 = true := by
  unfold fixInconsistencies
  generalize hm : mergeMoves ((sptToAList (sptUnion l r)).map Prod.fst) l r next = merged
  rcases merged with ⟨lmov, rmov, count, left, right⟩
  generalize hf : fakeMoves (width := width) prio ((sptToAList (sptUnion l r)).map Prod.fst)
    left right count = result
  rcases result with ⟨a, b, final, leftOut, rightOut⟩
  have facts := notCreated_fakeMoves P prio _ left right count a b final leftOut rightOut hf
  simpa [hm, hf, notCreatedSubprogsHOL] using facts

private theorem reconcileNotCreated (P : WordLangProgHOL (BitVec width) → Bool) {β : Type}
    (current target : Spt Nat) (names : Spt β) :
    notCreatedSubprogsHOL P (ssaReconcile current target names : WordLangProgHOL (BitVec width)) = true := by
  unfold ssaReconcile
  dsimp only
  split <;> simp [notCreatedSubprogsHOL]

private def programNotCreated (P : WordLangProgHOL (BitVec width) → Bool)
    (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ ssa next tables, notCreatedSubprogsHOL P prog = true →
    notCreatedSubprogsHOL P (ssaCcTrans prog ssa next tables).1 = true

/-- `ssa_cc_trans` keeps `not_created_subprogs` of the program component
    (Flapjack restatement of the HOL lemma below). -/
theorem notCreated_ssaCcTrans_fst (P : WordLangProgHOL (BitVec width) → Bool) :
    ∀ (prog : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (n : Nat)
      (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      notCreatedSubprogsHOL P prog = true → notCreatedSubprogsHOL P (ssaCcTrans prog ssa n lt).1 = true := by
  intro p
  apply WordLangProgHOL.rec
    (motive_1 := programNotCreated P)
    (motive_2 := fun ret => match ret with | none => True | some r => programNotCreated P r.2.2.1)
    (motive_3 := fun exc => match exc with | none => True | some r => programNotCreated P r.2.1)
    (motive_4 := fun r => programNotCreated P r.2.2.1)
    (motive_5 := fun r => programNotCreated P r.2.1)
    (motive_6 := fun r => programNotCreated P r.2.1)
    (motive_7 := fun r => programNotCreated P r.1) (t := p)
  all_goals dsimp only [programNotCreated]
  all_goals intros
  all_goals try simp_all [ssaCcTrans, notCreatedSubprogsHOL, nextVarRename, listNextVarRenameMove]
  case inst =>
    rename_i instruction ssa next tables
    exact notCreated_ssaCcTransInst P instruction ssa next _ _ _ rfl
  case ite =>
    exact fixNotCreated P _ _ _ _
  case loop =>
    rename_i names body exits ssa next tables bodyIH hb
    refine ⟨notCreated_loopSetup P names exits ssa next _ _ _ rfl, ?_⟩
    split
    · exact bodyIH _ _ _
    · simp only [notCreatedSubprogsHOL, Bool.and_eq_true]
      exact ⟨bodyIH _ _ _, reconcileNotCreated P _ _ _⟩
  case «break» | «continue» =>
    split
    · rfl
    · dsimp only
      split
      · rfl
      · simp only [notCreatedSubprogsHOL, Bool.and_true]
        exact reconcileNotCreated P _ _ _
  case shareInst =>
    split <;> simp_all [notCreatedSubprogsHOL]
  case call =>
    rename_i returns target arguments handler retIH excIH ssa next tables hc
    cases returns with
    | none =>
      cases handler with
      | none => simp_all [ssaCcTrans, notCreatedSubprogsHOL]
      | some exc =>
        rcases exc with ⟨excName, excBody, e1, e2⟩
        simp_all [ssaCcTrans, notCreatedSubprogsHOL]
    | some ret =>
      rcases ret with ⟨retNames, cutsets, retBody, l1, l2⟩
      cases handler with
      | none =>
        simp_all [ssaCcTrans, notCreatedSubprogsHOL, listNextVarRenameMove]
      | some exc =>
        rcases exc with ⟨excName, excBody, e1, e2⟩
        simp_all [ssaCcTrans, notCreatedSubprogsHOL, listNextVarRenameMove, nextVarRename,
          (fixNotCreated P _ _ _ _).1, (fixNotCreated P _ _ _ _).2]

/-- HOL `ssa_cc_trans_not_created_subprogs` (`wordConvsProofScript.sml:1176-1203`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "ssa_cc_trans_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_ssaCcTrans {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (prog : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (n : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit)) (prog' : WordLangProgHOL (BitVec width))
    (ssa' : Spt Nat) (na : Nat)
    (h : notCreatedSubprogsHOL P prog = true ∧ ssaCcTrans prog ssa n lt = (prog', ssa', na)) :
    notCreatedSubprogsHOL P prog' = true := by
  have := notCreated_ssaCcTrans_fst P prog ssa n lt h.1
  rw [h.2] at this
  exact this

/-- HOL `setup_ssa_not_created_subprogs` (`wordConvsProofScript.sml:1205-1215`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "setup_ssa_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_setupSSA {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool)
    (prog : WordLangProgHOL (BitVec width)) (n v : Nat) (mov : WordLangProgHOL (BitVec width))
    (ssa : Spt Nat) (na : Nat)
    (h : notCreatedSubprogsHOL P prog = true ∧ setupSSA (outputWidth := width) n v prog = (mov, ssa, na)) :
    notCreatedSubprogsHOL P mov = true := by
  obtain ⟨-, hs⟩ := h
  unfold setupSSA at hs
  generalize listNextVarRename (evenList n) .ln v = renamed at hs
  rcases renamed with ⟨names, tree, counter⟩
  cases hs
  rfl

/-- HOL `full_ssa_cc_trans_not_created_subprogs` (`wordConvsProofScript.sml:1217-1228`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "full_ssa_cc_trans_not_created_subprogs"
  (words_as_type_indexed_bitvec)]
theorem notCreated_fullSsaCcTrans {width : Nat} [NeZero width] (P : WordLangProgHOL (BitVec width) → Bool) (n : Nat)
    (prog : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P prog = true → notCreatedSubprogsHOL P (fullSsaCcTrans n prog) = true := by
  intro hp
  generalize produced : setupSSA (outputWidth := width) n (limitVar prog) prog = result
  rcases result with ⟨move, ssa, next⟩
  have hm := notCreated_setupSSA P prog n (limitVar prog) move ssa next ⟨hp, produced⟩
  have hb := notCreated_ssaCcTrans_fst P prog ssa next [] hp
  generalize bodyEq : ssaCcTrans prog ssa next [] = bodyResult
  rcases bodyResult with ⟨body, finalMap, finalNext⟩
  rw [bodyEq] at hb
  simp only [fullSsaCcTrans, produced, bodyEq, notCreatedSubprogsHOL, hm, hb, Bool.and_self]

end SSA

end Flapjack.WordConvs
