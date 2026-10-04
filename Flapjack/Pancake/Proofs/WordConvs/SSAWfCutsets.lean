import Flapjack.Pancake.Proofs.WordConvs.SSAFlatFull
import Flapjack.Pancake.WordConvs.WfCutsets
import Flapjack.Misc.Sptree.Wf

/-!
# `wordConvsProof` SSA well-formed cut sets

The `wf_cutsets` preservation theorems of the SSA section of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml` (`fake_seq_wf_cutsets`,
`ssa_reconcile_wf_cutsets`, `loop_setup_wf_cutsets`, `fake_moves_wf_cutsets`,
`ssa_cc_trans_wf_cutsets`, `full_ssa_cc_trans_wf_cutsets`). Every cut set the
SSA pass emits is rebuilt by `apply_nummaps_key`, a `fromAList`, hence `wf`.
-/

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

theorem wfNames_applyNummapsKey {α β : Type} (f : Nat → Nat) (names : Spt α × Spt β) :
    wfNames (applyNummapsKey f names) :=
  ⟨sptWfFromAList _, sptWfFromAList _⟩

/-- HOL `fake_seq_wf_cutsets` (`wordConvsProofScript.sml:1011-1015`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "fake_seq_wf_cutsets" (words_as_type_indexed_bitvec)]
theorem fakeSeq_wfCutsets {width : Nat} [NeZero width] (names : List Nat) :
    wfCutsets ((names.map (fakeMove : Nat → WordLangProgHOL (BitVec width))).foldr .seq .skip) := by
  induction names with
  | nil => simp [wfCutsets]
  | cons name names ih => simpa [wfCutsets, fakeMove] using ih

/-- HOL `ssa_reconcile_wf_cutsets` (`wordConvsProofScript.sml:1041-1045`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "ssa_reconcile_wf_cutsets" (words_as_type_indexed_bitvec)]
theorem ssaReconcile_wfCutsets {width : Nat} [NeZero width] {β : Type}
    (current target : Spt Nat) (names : Spt β) :
    wfCutsets (ssaReconcile current target names : WordLangProgHOL (BitVec width)) := by
  unfold ssaReconcile
  dsimp only
  split <;> simp [wfCutsets]

/-- HOL `loop_setup_wf_cutsets` (`wordConvsProofScript.sml:1091-1100`), with the
producer equation as sole premise. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "loop_setup_wf_cutsets" (words_as_type_indexed_bitvec)]
theorem loopSetup_wfCutsets {width : Nat} [NeZero width]
    (names exitNames : Spt Unit) (ssa : Spt Nat) (na : Nat)
    (setupProg : WordLangProgHOL (BitVec width)) (ssaRefreshed : Spt Nat)
    (naRefreshed : Nat)
    (setup : loopSetup names exitNames ssa na = (setupProg, ssaRefreshed, naRefreshed)) :
    wfCutsets setupProg := by
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
  have fake := fakeSeq_wfCutsets (width := width) fresh
  have moveConvention : wfCutsets moves := by
    unfold listNextVarRenameMove at hm
    have projected := congrArg Prod.fst hm
    simp only at projected
    rw [← projected]
    simp [wfCutsets]
  have output := congrArg Prod.fst setup
  simp only at output
  rw [← output]
  exact ⟨fake, moveConvention⟩

/-- HOL `fake_moves_wf_cutsets` (`wordConvsProofScript.sml:1477-1486`); HOL's free
`prio` is the leading binder. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "fake_moves_wf_cutsets" (words_as_type_indexed_bitvec)]
theorem fakeMoves_wfCutsets {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit)) :
    ∀ (ls : List Nat) (A B : Spt Nat) (C : Nat) (L R : WordLangProgHOL (BitVec width)) (D : Nat)
      (E G : Spt Nat),
      fakeMoves prio ls A B C = (L, R, D, E, G) → wfCutsets L ∧ wfCutsets R := by
  have all : ∀ (ls : List Nat) (l r : Spt Nat) (na : Nat),
      let (a, b, _, _, _) := fakeMoves (width := width) prio ls l r na
      wfCutsets a ∧ wfCutsets b := by
    intro ls
    induction ls with
    | nil => intro l r na; simp [fakeMoves, wfCutsets]
    | cons x xs ih =>
        intro l r na
        generalize he : fakeMoves (width := width) prio xs l r na = result
        rcases result with ⟨a, b, count, treeL, treeR⟩
        have previous := ih l r na
        rw [he] at previous
        simp only [fakeMoves, he]
        cases hl : sptLookup x treeL <;> cases hr : sptLookup x treeR <;>
          simp_all [wfCutsets, fakeMove]
  intro ls A B C L R D E G h
  have result := all ls A B C
  rw [h] at result
  exact result

private theorem fixWf {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (l r : Spt Nat) (next : Nat) :
    let out := fixInconsistencies (width := width) prio l r next
    wfCutsets out.1 ∧ wfCutsets out.2.1 := by
  unfold fixInconsistencies
  generalize hm : mergeMoves ((sptToAList (sptUnion l r)).map Prod.fst) l r next = merged
  rcases merged with ⟨lmov, rmov, count, left, right⟩
  generalize hf : fakeMoves (width := width) prio ((sptToAList (sptUnion l r)).map Prod.fst)
    left right count = result
  rcases result with ⟨a, b, final, leftOut, rightOut⟩
  have facts := fakeMoves_wfCutsets prio _ left right count a b final leftOut rightOut hf
  simpa [hm, hf, wfCutsets] using facts

private def programWf {width : Nat} [NeZero width] (program : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ ssa next tables, wfCutsets (ssaCcTrans program ssa next tables).1

/-- HOL `ssa_cc_trans_wf_cutsets` (`wordConvsProofScript.sml:1487-1503`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "ssa_cc_trans_wf_cutsets" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_wfCutsets {width : Nat} [NeZero width] :
    ∀ (prog : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (na : Nat)
      (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      wfCutsets (ssaCcTrans prog ssa na lt).1 := by
  intro p
  apply WordLangProgHOL.rec
    (motive_1 := programWf)
    (motive_2 := fun ret => match ret with | none => True | some r => programWf r.2.2.1)
    (motive_3 := fun exc => match exc with | none => True | some r => programWf r.2.1)
    (motive_4 := fun r => programWf r.2.2.1)
    (motive_5 := fun r => programWf r.2.1)
    (motive_6 := fun r => programWf r.2.1)
    (motive_7 := fun r => programWf r.1) (t := p)
  all_goals dsimp only [programWf]
  all_goals intros
  all_goals try simp_all [ssaCcTrans, wfCutsets, nextVarRename, listNextVarRenameMove,
    wfNames_applyNummapsKey]
  case inst =>
    rename_i instruction tree counter context
    fun_cases ssaCcTransInst instruction tree counter <;> simp [wfCutsets]
  case ite =>
    exact fixWf _ _ _ _
  case «break» =>
    split <;> simp_all [wfCutsets]
    split <;> simp_all [wfCutsets, ssaReconcile_wfCutsets]
  case «continue» =>
    split <;> simp_all [wfCutsets]
    split <;> simp_all [wfCutsets, ssaReconcile_wfCutsets]
  case loop =>
    rename_i names body exits bodyIH tree counter context
    generalize setupEq : loopSetup (width := width) names exits tree counter = setupOut at *
    rcases setupOut with ⟨setupProg, setupTree, setupNext⟩
    have setupWf := loopSetup_wfCutsets (width := width) names exits tree counter
      setupProg setupTree setupNext setupEq
    have bodyWf := bodyIH (sptInter setupTree names) setupNext
      ((setupTree, names, exits) :: context)
    generalize bodyEq : ssaCcTrans body (sptInter setupTree names) setupNext
      ((setupTree, names, exits) :: context) = bodyOut at *
    rcases bodyOut with ⟨bodyProg, bodyTree, bodyNext⟩
    have backWf := ssaReconcile_wfCutsets (width := width) bodyTree setupTree names
    generalize backEq : ssaReconcile (width := width) bodyTree setupTree names = back at *
    simp only [applyNummapKey]
    cases back <;> simp_all [wfCutsets, sptWfFromAList]
  case shareInst =>
    split <;> simp [wfCutsets]
  case call =>
    rename_i returns target arguments handler retIH excIH tree counter context
    cases returns with
    | none => simp [ssaCcTrans, wfCutsets]
    | some ret =>
      rcases ret with ⟨retNames, cutsets, retBody, l1, l2⟩
      cases handler with
      | none =>
        simp_all [ssaCcTrans, wfCutsets, listNextVarRenameMove, wfNames_applyNummapsKey]
      | some exc =>
        rcases exc with ⟨excName, excBody, e1, e2⟩
        simp_all [ssaCcTrans, wfCutsets, listNextVarRenameMove, nextVarRename,
          wfNames_applyNummapsKey, (fixWf _ _ _ _).1, (fixWf _ _ _ _).2]

/-- HOL `full_ssa_cc_trans_wf_cutsets` (`wordConvsProofScript.sml:1505-1516`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "full_ssa_cc_trans_wf_cutsets" (words_as_type_indexed_bitvec)]
theorem fullSsaCcTrans_wfCutsets {width : Nat} [NeZero width] :
    ∀ (n : Nat) (prog : WordLangProgHOL (BitVec width)), wfCutsets (fullSsaCcTrans n prog) := by
  intro count program
  generalize produced : setupSSA (outputWidth := width) count (limitVar program) program = result
  rcases result with ⟨move, ssa, next⟩
  have moveWf : wfCutsets move := by
    unfold setupSSA at produced
    generalize listNextVarRename (evenList count) .ln (limitVar program) = renamed at produced
    rcases renamed with ⟨names, tree, counter⟩
    cases produced
    simp [wfCutsets]
  have bodyWf := ssaCcTrans_wfCutsets program ssa next []
  generalize bodyEq : ssaCcTrans program ssa next [] = bodyResult
  rcases bodyResult with ⟨body, finalMap, finalNext⟩
  rw [bodyEq] at bodyWf
  simp only [fullSsaCcTrans, produced, bodyEq, wfCutsets]
  exact ⟨moveWf, bodyWf⟩

end Flapjack.WordAlloc
