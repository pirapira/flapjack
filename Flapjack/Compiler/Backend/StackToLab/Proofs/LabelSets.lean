import Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Statement
import Flapjack.Compiler.Backend.LabProps.LabelSets
import Flapjack.Compiler.Backend.StackProps.CodeLabels
import Flapjack.Compiler.Backend.StackProps.LabelSafety

/-! The label-set group of `stack_to_labProofScript.sml:3800-4089`: the labels
referenced by flattened code are its own code labels, the enclosing loop
labels, or labels referenced by the source program. HOL sets are Lean `Set`s;
`BIGUNION (IMAGE f s)` is `⋃₀ (f '' s)` and `set l` is `{x | x ∈ l}`. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.LabelSets
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled

attribute [local simp] FlattenCorrect.appListAppendAppend FlattenCorrect.appListAppendList

/-- HOL `complex_get_code_labels_def`. HOL `INSERT` binds looser than
`UNION`, so the return clause is `(l1,l2) INSERT (labels of r ∪ handler
labels)`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "complex_get_code_labels_def"
  (words_as_type_indexed_bitvec)]
def complexGetCodeLabels {width : Nat} [NeZero width] : HolProg width → Set (Nat × Nat)
  | .seq p1 p2 => complexGetCodeLabels p1 ∪ complexGetCodeLabels p2
  | .ite _ _ _ p1 p2 => complexGetCodeLabels p1 ∪ complexGetCodeLabels p2
  | .call ret dest handler =>
      (match dest with
        | .inl x => {(x, 0)}
        | .inr _ => ∅) ∪
      (match ret with
        | none => ∅
        | some (r, _, l1, l2) => insert (l1, l2) (complexGetCodeLabels r ∪
            (match handler with
              | none => ∅
              | some (r, l1, l2) => insert (l1, l2) (complexGetCodeLabels r))))
  | .loop p => complexGetCodeLabels p
  | .locValue _ l1 l2 => {(l1, l2)}
  | .rawCall l => {(l, 1)}
  | .jumpLower _ _ l => {(l, 0)}
  | _ => ∅

open Classical in
/-- The right-hand side of `complex_flatten_labels` over an arbitrary line
list (Flapjack infrastructure). -/
def rhs {width : Nat} [NeZero width] (t : Bool) (p : HolProg width) (n : Nat) (cs bs : List Nat)
    (out : List (LabSem.LabLineHOL width)) : Set (Nat × Nat) :=
  insert (n, 0) (insert (n, if t = true ∧ ∃ p1 p2, p = .seq p1 p2 then 1 else 0)
    ({x | x ∈ (cs ++ bs).map (fun l => (n, l))} ∪
      (fun n2 => (n, n2)) '' ⋃₀ (lineGetCodeLabels '' {ln | ln ∈ out}) ∪
      complexGetCodeLabels p))

theorem codeLabel_mem_rhs {width : Nat} [NeZero width] {t : Bool} {p : HolProg width}
    {n : Nat} {cs bs : List Nat} {out : List (LabSem.LabLineHOL width)} {s l e : Nat}
    (h : Line.label s l e ∈ out) : (n, l) ∈ rhs t p n cs bs out := by
  simp only [rhs, Set.mem_insert_iff, Set.mem_union, Set.mem_image, Set.mem_sUnion,
    Set.mem_ofPred_eq]
  exact .inr (.inr (.inl (.inr ⟨l, ⟨_, ⟨_, h, rfl⟩, by simp [lineGetCodeLabels]⟩, rfl⟩)))

theorem complex_mem_rhs {width : Nat} [NeZero width] {t : Bool} {p : HolProg width}
    {n : Nat} {cs bs : List Nat} {out : List (LabSem.LabLineHOL width)} {x : Nat × Nat}
    (h : x ∈ complexGetCodeLabels p) : x ∈ rhs t p n cs bs out := by
  simp only [rhs, Set.mem_insert_iff, Set.mem_union]
  exact .inr (.inr (.inr h))

/-- Lifting a sub-flattening's bound into the enclosing one. -/
theorem rhs_lift {width : Nat} [NeZero width] {t : Bool} {p q : HolProg width}
    {n : Nat} {cs bs cs' bs' : List Nat} {out out' : List (LabSem.LabLineHOL width)}
    (hlines : ∀ ln ∈ out', ln ∈ out)
    (hcs : ∀ l ∈ cs' ++ bs', (n, l) ∈ rhs t p n cs bs out)
    (hcx : complexGetCodeLabels q ⊆ complexGetCodeLabels p) :
    rhs false q n cs' bs' out' ⊆ rhs t p n cs bs out := by
  intro x hx
  simp only [rhs, Bool.false_eq_true, false_and, if_false, Set.mem_insert_iff, Set.mem_union,
    Set.mem_ofPred_eq, Set.mem_image, Set.mem_sUnion, List.mem_map] at hx
  rcases hx with rfl | rfl | ((⟨l, hl, rfl⟩ | ⟨n2, ⟨_, ⟨ln, hln, rfl⟩, hn2⟩, rfl⟩) | hc)
  · simp [rhs]
  · simp [rhs]
  · exact hcs l hl
  · simp only [rhs, Set.mem_insert_iff, Set.mem_union, Set.mem_image, Set.mem_sUnion,
      Set.mem_ofPred_eq]
    exact .inr (.inr (.inl (.inr ⟨n2, ⟨_, ⟨ln, hlines ln hln, rfl⟩, hn2⟩, rfl⟩)))
  · exact complex_mem_rhs (hcx hc)

theorem zero_mem_rhs {width : Nat} [NeZero width] {t : Bool} {p : HolProg width}
    {n : Nat} {cs bs : List Nat} {out : List (LabSem.LabLineHOL width)} :
    (n, 0) ∈ rhs t p n cs bs out := by
  simp [rhs]

theorem stack_mem_rhs {width : Nat} [NeZero width] {t : Bool} {p : HolProg width}
    {n : Nat} {cs bs : List Nat} {out : List (LabSem.LabLineHOL width)} {l : Nat}
    (h : l ∈ cs ++ bs) : (n, l) ∈ rhs t p n cs bs out := by
  simp only [rhs, Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq, List.mem_map]
  exact .inr (.inr (.inl (.inl ⟨l, h, rfl⟩)))

theorem findLab_cases (i : Nat) (L : List Nat) : findLabHOL i L = 0 ∨ findLabHOL i L ∈ L := by
  unfold findLabHOL
  cases h : L[i]? with
  | none => exact .inl rfl
  | some v => exact .inr (List.mem_of_getElem? h)

theorem findLab_conts_mem_rhs {width : Nat} [NeZero width] {t : Bool} {p : HolProg width}
    {n : Nat} {cs bs : List Nat} {out : List (LabSem.LabLineHOL width)} (i : Nat) :
    (n, findLabHOL i cs) ∈ rhs t p n cs bs out := by
  rcases findLab_cases i cs with h | h
  · rw [h]; exact zero_mem_rhs
  · exact stack_mem_rhs (by simp [h])

theorem findLab_breaks_mem_rhs {width : Nat} [NeZero width] {t : Bool} {p : HolProg width}
    {n : Nat} {cs bs : List Nat} {out : List (LabSem.LabLineHOL width)} (i : Nat) :
    (n, findLabHOL i bs) ∈ rhs t p n cs bs out := by
  rcases findLab_cases i bs with h | h
  · rw [h]; exact zero_mem_rhs
  · exact stack_mem_rhs (by simp [h])

theorem compileJump_labels {width : Nat} [NeZero width] (target : Nat ⊕ Nat)
    (ret : Option (HolProg width × Nat × Nat × Nat)) (handler : Option (HolProg width × Nat × Nat))
    {x : Nat × Nat} (h : x ∈ lineGetLabels (compileJumpHOL (width := width) target)) :
    x ∈ complexGetCodeLabels (.call ret target handler) := by
  cases target with
  | inl v =>
    simp only [compileJumpHOL, lineGetLabels, labsOf, Set.mem_singleton_iff] at h
    subst h
    rw [complexGetCodeLabels.eq_def]
    simp
  | inr r => simp [compileJumpHOL, lineGetLabels] at h

set_option maxHeartbeats 1000000 in
theorem flattenLabelsCore {width : Nat} [NeZero width] :
    ∀ (t : Bool) (p : HolProg width) (n m : Nat) (cs bs : List Nat),
      ∀ ln ∈ appListAppend (flattenHOL t p n m cs bs).1,
        lineGetLabels ln ⊆ rhs t p n cs bs (appListAppend (flattenHOL t p n m cs bs).1) := by
  intro t p n m cs bs
  induction t, p, m, cs, bs using flattenHOL.induct n
  case case26 =>
    rw [flattenHOL]
    all_goals (try assumption)
    intro ln hln
    simp at hln
  all_goals (try rename_i ih2 ih1)
  all_goals
    rw [flattenHOL]
    try simp (config := { zetaDelta := true }) only [*] at *
  all_goals (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split)
  all_goals intro ln hln
  all_goals (try simp only [FlattenCorrect.appListAppendList, FlattenCorrect.appListAppendAppend,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln)
  case case11 =>
    rcases hln with (rfl | h) | rfl | rfl
    · simp [lineGetLabels]
    · intro x hx
      refine rhs_lift (fun l hl => by simp [hl]) (fun l hl => ?_)
        (fun y hy => by simpa [complexGetCodeLabels] using hy) (ih1 _ h hx)
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hl
      rcases hl with rfl | hl | rfl | hl
      · exact codeLabel_mem_rhs (s := n) (e := 0) (by simp)
      · exact stack_mem_rhs (by simp [hl])
      · exact codeLabel_mem_rhs (s := n) (e := 0) (by simp)
      · exact stack_mem_rhs (by simp [hl])
    · simp only [lineGetLabels, labsOf, Set.singleton_subset_iff]
      exact codeLabel_mem_rhs (s := n) (e := 0) (by simp)
    · simp [lineGetLabels]
  all_goals intro x hx
  all_goals repeat' (rcases (hln : _ ∨ _) with hln | hln)
  all_goals first
    | (subst hln; simp [lineGetLabels, labsOf, compileJumpHOL] at hx; done)
    | (subst hln; exact complex_mem_rhs (compileJump_labels _ _ _ hx))
    | (subst hln; simp only [lineGetLabels, labsOf, Set.mem_singleton_iff] at hx; subst hx
       first
       | exact findLab_conts_mem_rhs _
       | exact findLab_breaks_mem_rhs _)
    | (subst hln; simp only [lineGetLabels, labsOf, Set.mem_singleton_iff] at hx; subst hx
       first
       | exact zero_mem_rhs
       | (apply codeLabel_mem_rhs (s := n) (e := 0); simp)
       | (apply complex_mem_rhs; simp [complexGetCodeLabels]))
    | (first
       | (have hI := ih1 _ hln hx
          refine rhs_lift ?_ (fun l hl => stack_mem_rhs hl) ?_ hI
          · intro l hl; simp [hl]
          · intro y hy; simp [complexGetCodeLabels, hy])
       | (have hI := ih2 _ hln hx
          refine rhs_lift ?_ (fun l hl => stack_mem_rhs hl) ?_ hI
          · intro l hl; simp [hl]
          · intro y hy; simp [complexGetCodeLabels, hy]))

open Classical in
/-- HOL `complex_flatten_labels` (local). The `let pp = set (...)` is inlined
as the membership predicate of the flattened lines; `INSERT`/`UNION`
association as in HOL (`INSERT` looser than `UNION`). -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "complex_flatten_labels"
  (words_as_type_indexed_bitvec)]
theorem complexFlattenLabels {width : Nat} [NeZero width] :
    ∀ (t : Bool) (p : HolProg width) (n m : Nat) (cs bs : List Nat),
      ⋃₀ (lineGetLabels '' {ln | ln ∈ appListAppend (flattenHOL t p n m cs bs).1}) ⊆
        insert (n, 0) (insert (n, if t = true ∧ ∃ p1 p2, p = .seq p1 p2 then 1 else 0)
          ({x | x ∈ (cs ++ bs).map (fun l => (n, l))} ∪
            (fun n2 => (n, n2)) '' ⋃₀ (lineGetCodeLabels ''
              {ln | ln ∈ appListAppend (flattenHOL t p n m cs bs).1}) ∪
            complexGetCodeLabels p)) := by
  rintro t p n m cs bs x ⟨_, ⟨ln, hln, rfl⟩, hx⟩
  exact flattenLabelsCore t p n m cs bs ln hln hx

theorem complex_of_isSkip {width : Nat} [NeZero width] {p : HolProg width}
    (h : stackIsSkip p = true) : complexGetCodeLabels p = ∅ := by
  cases p <;> simp_all [stackIsSkip, complexGetCodeLabels]

/-- Labels of `complexGetCodeLabels` are referenced code labels of the
program or labels placed in its flattening (Flapjack infrastructure for
`flatten_labels`). -/
theorem complexLabelsPlaced {width : Nat} [NeZero width] :
    ∀ (p : HolProg width) (t : Bool) (n m : Nat) (cs bs : List Nat),
      ∀ lab ∈ complexGetCodeLabels p, lab ∈ StackProps.getCodeLabels p ∨
        ∃ e, Line.label lab.1 lab.2 e ∈ appListAppend (flattenHOL t p n m cs bs).1
  | .seq a b, t, n, m, cs, bs, lab, h => by
      rw [complexGetCodeLabels] at h
      rw [flattenHOL]
      rcases ha : flattenHOL false a n m cs bs with ⟨xs, nr1, m1⟩
      rcases hb : flattenHOL false b n m1 cs bs with ⟨ys, nr2, m2⟩
      simp only [hb]
      rcases h with h | h
      · rcases complexLabelsPlaced a false n m cs bs lab h with h' | ⟨e, he⟩
        · exact .inl (by rw [StackProps.getCodeLabels]; exact .inl h')
        · rw [ha] at he; simp only at he; refine .inr ⟨e, ?_⟩; split <;> simp [he]
      · rcases complexLabelsPlaced b false n m1 cs bs lab h with h' | ⟨e, he⟩
        · exact .inl (by rw [StackProps.getCodeLabels]; exact .inr h')
        · rw [hb] at he; simp only at he; refine .inr ⟨e, ?_⟩; split <;> simp [he]
  | .loop body, t, n, m, cs, bs, lab, h => by
      rw [complexGetCodeLabels] at h
      rw [flattenHOL]
      rcases hb : flattenHOL false body n (m + 2) (m :: cs) ((m + 1) :: bs) with ⟨xs, nr, m1⟩
      simp only
      rcases complexLabelsPlaced body false n (m + 2) (m :: cs) ((m + 1) :: bs) lab h with
        h' | ⟨e, he⟩
      · exact .inl (by rw [StackProps.getCodeLabels]; exact h')
      · rw [hb] at he; simp only at he; refine .inr ⟨e, ?_⟩; simp [he]
  | .ite c r ri a b, t, n, m, cs, bs, lab, h => by
      rw [complexGetCodeLabels] at h
      rw [flattenHOL]
      rcases ha : flattenHOL false a n m cs bs with ⟨xs, nr1, m1⟩
      rcases hb : flattenHOL false b n m1 cs bs with ⟨ys, nr2, m2⟩
      simp only [hb]
      rcases h with h | h
      · rcases complexLabelsPlaced a false n m cs bs lab h with h' | ⟨e, he⟩
        · exact .inl (by rw [StackProps.getCodeLabels]; exact .inl h')
        · rw [ha] at he; simp only at he; refine .inr ⟨e, ?_⟩
          split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
            simp_all [complex_of_isSkip]
      · rcases complexLabelsPlaced b false n m1 cs bs lab h with h' | ⟨e, he⟩
        · exact .inl (by rw [StackProps.getCodeLabels]; exact .inr h')
        · rw [hb] at he; simp only at he; refine .inr ⟨e, ?_⟩
          split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
            simp_all [complex_of_isSkip]
  | .call none d hd, t, n, m, cs, bs, lab, h => by
      left
      rw [complexGetCodeLabels.eq_def] at h
      rw [StackProps.getCodeLabels.eq_def]
      cases d <;> simp_all
  | .call (some (rp, lr, l1, l2)) d none, t, n, m, cs, bs, lab, h => by
      rw [complexGetCodeLabels.eq_def] at h
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at h
      rw [flattenHOL]
      rcases hr : flattenHOL false rp n m cs bs with ⟨xs, nr1, m1⟩
      simp only
      rcases h with h | rfl | h
      · left; rw [StackProps.getCodeLabels.eq_def]; cases d <;> simp_all
      · right; exact ⟨0, by simp⟩
      · rcases complexLabelsPlaced rp false n m cs bs lab h with h' | ⟨e, he⟩
        · left; rw [StackProps.getCodeLabels.eq_def]; simp [h']
        · rw [hr] at he; simp only at he; right; exact ⟨e, by simp [he]⟩
  | .call (some (rp, lr, l1, l2)) d (some (hp, hl1, hl2)), t, n, m, cs, bs, lab, h => by
      rw [complexGetCodeLabels.eq_def] at h
      simp only [Set.mem_union, Set.mem_insert_iff] at h
      rw [flattenHOL]
      rcases hr : flattenHOL false rp n m cs bs with ⟨xs, nr1, m1⟩
      rcases hh : flattenHOL false hp n m1 cs bs with ⟨ys, nr2, m2⟩
      simp only [hh]
      rcases h with h | rfl | h | rfl | h
      · left; rw [StackProps.getCodeLabels.eq_def]; cases d <;> simp_all
      · right; exact ⟨0, by simp⟩
      · rcases complexLabelsPlaced rp false n m cs bs lab h with h' | ⟨e, he⟩
        · left; rw [StackProps.getCodeLabels.eq_def]; simp [h']
        · rw [hr] at he; simp only at he; right; exact ⟨e, by simp [he]⟩
      · right; exact ⟨0, by simp⟩
      · rcases complexLabelsPlaced hp false n m1 cs bs lab h with h' | ⟨e, he⟩
        · left; rw [StackProps.getCodeLabels.eq_def]; simp [h']
        · rw [hh] at he; simp only at he; right; exact ⟨e, by simp [he]⟩
  | .locValue _ _ _, _, _, _, _, _, lab, h | .rawCall _, _, _, _, _, _, lab, h
  | .jumpLower _ _ _, _, _, _, _, _, lab, h => by
      left; simpa [complexGetCodeLabels, StackProps.getCodeLabels] using h
  | .skip, _, _, _, _, _, _, h | .inst _, _, _, _, _, _, _, h | .get _ _, _, _, _, _, _, _, h
  | .set _ _, _, _, _, _, _, _, h | .opCurrHeap _ _ _, _, _, _, _, _, _, h
  | .alloc _, _, _, _, _, _, _, h | .storeConsts _ _ _, _, _, _, _, _, _, h
  | .raise _, _, _, _, _, _, _, h | .ret _, _, _, _, _, _, _, h | .break _, _, _, _, _, _, _, h
  | .continue _, _, _, _, _, _, _, h | .ffi _ _ _ _ _ _, _, _, _, _, _, _, h
  | .tick, _, _, _, _, _, _, h | .install _ _ _ _ _, _, _, _, _, _, _, h
  | .shMemOp _ _ _, _, _, _, _, _, _, h | .codeBufferWrite _ _, _, _, _, _, _, _, h
  | .dataBufferWrite _ _, _, _, _, _, _, _, h | .stackAlloc _, _, _, _, _, _, _, h
  | .stackFree _, _, _, _, _, _, _, h | .stackStore _ _, _, _, _, _, _, _, h
  | .stackStoreAny _ _, _, _, _, _, _, _, h | .stackLoad _ _, _, _, _, _, _, _, h
  | .stackLoadAny _ _, _, _, _, _, _, _, h | .stackGetSize _, _, _, _, _, _, _, h
  | .stackSetSize _, _, _, _, _, _, _, h | .bitmapLoad _ _, _, _, _, _, _, _, h
  | .halt _, _, _, _, _, _, _, h => by
      simp [complexGetCodeLabels] at h
termination_by p => sizeOf p

/-- HOL `flatten_labels` (local). HOL's variable names are kept: `m` is the
program, `n` the section and `p` the next label. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_labels"
  (words_as_type_indexed_bitvec)]
theorem flattenLabels {width : Nat} [NeZero width] :
    ∀ (t : Bool) (m : HolProg width) (n p : Nat) (cs bs : List Nat)
      (l : AppList (LabSem.LabLineHOL width)) (x : Bool) (y : Nat),
      flattenHOL t m n p cs bs = (l, x, y) ∧
        (∀ ln ∈ appListAppend l, LabProps.secLabelOk n ln) →
      ⋃₀ (lineGetLabels '' {ln | ln ∈ appListAppend l}) ⊆
        {z | z ∈ (cs ++ bs).map (fun l => (n, l))} ∪ secGetCodeLabels ⟨n, appListAppend l⟩ ∪
          StackProps.getCodeLabels m := by
  rintro t m n p cs bs l x y ⟨hf, hok⟩ lab ⟨_, ⟨ln, hln, rfl⟩, hx⟩
  have hcore := flattenLabelsCore t m n p cs bs ln (by rw [hf]; exact hln) hx
  rw [hf] at hcore
  have mid : ∀ n2, (∃ ln' ∈ appListAppend l, n2 ∈ lineGetCodeLabels ln') →
      (n, n2) ∈ {z | z ∈ (cs ++ bs).map (fun l => (n, l))} ∪ secGetCodeLabels ⟨n, appListAppend l⟩ ∪
        StackProps.getCodeLabels m := by
    rintro n2 ⟨ln', hl', hn2⟩
    exact .inl (.inr (.inr ⟨n2, ⟨ln', hl', hn2⟩, rfl⟩))
  simp only [rhs, Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq, List.mem_map,
    Set.mem_image, Set.mem_sUnion] at hcore
  rcases hcore with rfl | rfl | ((⟨l', hl', rfl⟩ | ⟨n2, ⟨_, ⟨ln', hl', rfl⟩, hn2⟩, rfl⟩) | hc)
  · exact .inl (.inr (.inl rfl))
  · split
    · rename_i hseq
      obtain ⟨rfl, a, b, rfl⟩ := hseq
      refine mid 1 ⟨.label n 1 0, ?_, by simp [lineGetCodeLabels]⟩
      rw [flattenHOL] at hf
      simp only at hf
      rw [← (Prod.mk.inj hf).1]
      simp
    · exact .inl (.inr (.inl rfl))
  · exact .inl (.inl (List.mem_map.mpr ⟨l', hl', rfl⟩))
  · exact mid n2 ⟨ln', hl', hn2⟩
  · rcases complexLabelsPlaced m t n p cs bs lab hc with h | ⟨e, he⟩
    · exact .inr h
    · rw [hf] at he
      have hl := hok _ he
      simp only [LabProps.secLabelOk] at hl
      obtain ⟨l1, l2⟩ := lab
      simp only at hl he
      rw [hl.1]
      exact mid l2 ⟨_, he, by simp [lineGetCodeLabels]⟩

/-- Owned handler labels have their `Label` line in the flattening
(Flapjack infrastructure for `flatten_preserves_handler_labels`). -/
theorem handlerLabelsPlaced {width : Nat} [NeZero width] :
    ∀ (p : HolProg width) (t : Bool) (n m : Nat) (cs bs : List Nat),
      ∀ lab ∈ StackProps.stackGetHandlerLabels n p, lab.1 = n ∧
        ∃ e, Line.label lab.1 lab.2 e ∈ appListAppend (flattenHOL t p n m cs bs).1
  | .seq a b, t, n, m, cs, bs, lab, h => by
      rw [StackProps.stackGetHandlerLabels] at h
      rw [flattenHOL]
      rcases ha : flattenHOL false a n m cs bs with ⟨xs, nr1, m1⟩
      rcases hb : flattenHOL false b n m1 cs bs with ⟨ys, nr2, m2⟩
      simp only [hb]
      rcases h with h | h
      · obtain ⟨h1, e, he⟩ := handlerLabelsPlaced a false n m cs bs lab h
        rw [ha] at he; simp only at he
        exact ⟨h1, e, by split <;> simp [he]⟩
      · obtain ⟨h1, e, he⟩ := handlerLabelsPlaced b false n m1 cs bs lab h
        rw [hb] at he; simp only at he
        exact ⟨h1, e, by split <;> simp [he]⟩
  | .ite c r ri a b, t, n, m, cs, bs, lab, h => by
      rw [StackProps.stackGetHandlerLabels] at h
      rw [flattenHOL]
      rcases ha : flattenHOL false a n m cs bs with ⟨xs, nr1, m1⟩
      rcases hb : flattenHOL false b n m1 cs bs with ⟨ys, nr2, m2⟩
      simp only [hb]
      rcases h with h | h
      · obtain ⟨h1, e, he⟩ := handlerLabelsPlaced a false n m cs bs lab h
        rw [ha] at he; simp only at he
        refine ⟨h1, e, ?_⟩
        split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
          simp_all
        all_goals (rename_i hs _
                   cases a <;> simp_all [stackIsSkip, StackProps.stackGetHandlerLabels])
      · obtain ⟨h1, e, he⟩ := handlerLabelsPlaced b false n m1 cs bs lab h
        rw [hb] at he; simp only at he
        refine ⟨h1, e, ?_⟩
        split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
          simp_all
        all_goals (cases b <;> simp_all [stackIsSkip, StackProps.stackGetHandlerLabels])
  | .loop body, t, n, m, cs, bs, lab, h => by
      rw [StackProps.stackGetHandlerLabels] at h
      rw [flattenHOL]
      rcases hb : flattenHOL false body n (m + 2) (m :: cs) ((m + 1) :: bs) with ⟨xs, nr, m1⟩
      simp only
      obtain ⟨h1, e, he⟩ := handlerLabelsPlaced body false n (m + 2) (m :: cs) ((m + 1) :: bs) lab h
      rw [hb] at he; simp only at he
      exact ⟨h1, e, by simp [he]⟩
  | .call none d hd, t, n, m, cs, bs, lab, h => by
      simp [StackProps.stackGetHandlerLabels] at h
  | .call (some (rp, lr, l1, l2)) d none, t, n, m, cs, bs, lab, h => by
      simp only [StackProps.stackGetHandlerLabels, Set.union_empty] at h
      rw [flattenHOL]
      rcases hr : flattenHOL false rp n m cs bs with ⟨xs, nr1, m1⟩
      simp only
      obtain ⟨h1, e, he⟩ := handlerLabelsPlaced rp false n m cs bs lab h
      rw [hr] at he; simp only at he
      exact ⟨h1, e, by simp [he]⟩
  | .call (some (rp, lr, l1, l2)) d (some (hp, hl1, hl2)), t, n, m, cs, bs, lab, h => by
      simp only [StackProps.stackGetHandlerLabels, Set.mem_union] at h
      rw [flattenHOL]
      rcases hr : flattenHOL false rp n m cs bs with ⟨xs, nr1, m1⟩
      rcases hh : flattenHOL false hp n m1 cs bs with ⟨ys, nr2, m2⟩
      simp only [hh]
      rcases h with h | h | h
      · obtain ⟨h1, e, he⟩ := handlerLabelsPlaced rp false n m cs bs lab h
        rw [hr] at he; simp only at he
        exact ⟨h1, e, by simp [he]⟩
      · split at h
        · rename_i heq
          simp only [Set.mem_singleton_iff] at h
          subst h
          exact ⟨heq, 0, by simp⟩
        · simp at h
      · obtain ⟨h1, e, he⟩ := handlerLabelsPlaced hp false n m1 cs bs lab h
        rw [hh] at he; simp only at he
        exact ⟨h1, e, by simp [he]⟩
  | .locValue _ _ _, _, _, _, _, _, _, h | .rawCall _, _, _, _, _, _, _, h
  | .jumpLower _ _ _, _, _, _, _, _, _, h
  | .skip, _, _, _, _, _, _, h | .inst _, _, _, _, _, _, _, h | .get _ _, _, _, _, _, _, _, h
  | .set _ _, _, _, _, _, _, _, h | .opCurrHeap _ _ _, _, _, _, _, _, _, h
  | .alloc _, _, _, _, _, _, _, h | .storeConsts _ _ _, _, _, _, _, _, _, h
  | .raise _, _, _, _, _, _, _, h | .ret _, _, _, _, _, _, _, h | .break _, _, _, _, _, _, _, h
  | .continue _, _, _, _, _, _, _, h | .ffi _ _ _ _ _ _, _, _, _, _, _, _, h
  | .tick, _, _, _, _, _, _, h | .install _ _ _ _ _, _, _, _, _, _, _, h
  | .shMemOp _ _ _, _, _, _, _, _, _, h | .codeBufferWrite _ _, _, _, _, _, _, _, h
  | .dataBufferWrite _ _, _, _, _, _, _, _, h | .stackAlloc _, _, _, _, _, _, _, h
  | .stackFree _, _, _, _, _, _, _, h | .stackStore _ _, _, _, _, _, _, _, h
  | .stackStoreAny _ _, _, _, _, _, _, _, h | .stackLoad _ _, _, _, _, _, _, _, h
  | .stackLoadAny _ _, _, _, _, _, _, _, h | .stackGetSize _, _, _, _, _, _, _, h
  | .stackSetSize _, _, _, _, _, _, _, h | .bitmapLoad _ _, _, _, _, _, _, _, h
  | .halt _, _, _, _, _, _, _, h => by
      simp [StackProps.stackGetHandlerLabels] at h
termination_by p => sizeOf p

/-- HOL `flatten_preserves_handler_labels`. HOL's names: `m` is the program,
`n` the section and `p` the next label. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "flatten_preserves_handler_labels"
  (words_as_type_indexed_bitvec)]
theorem flattenPreservesHandlerLabels {width : Nat} [NeZero width] :
    ∀ (t : Bool) (m : HolProg width) (n p : Nat) (cs bs : List Nat)
      (l : AppList (LabSem.LabLineHOL width)) (x : Bool) (y : Nat),
      flattenHOL t m n p cs bs = (l, x, y) →
      StackProps.stackGetHandlerLabels n m ⊆ secGetCodeLabels ⟨n, appListAppend l⟩ := by
  intro t m n p cs bs l x y hf lab hlab
  obtain ⟨h1, e, he⟩ := handlerLabelsPlaced m t n p cs bs lab hlab
  rw [hf] at he
  obtain ⟨l1, l2⟩ := lab
  simp only at h1 he
  subst h1
  exact .inr ⟨l2, ⟨_, he, by simp [lineGetCodeLabels]⟩, rfl⟩

/-- A section's code labels grow with its lines (Flapjack infrastructure). -/
theorem secGetCodeLabels_mono {width : Nat} [NeZero width] {n : Nat}
    {xs ys : List (LabSem.LabLineHOL width)} (h : ∀ x ∈ xs, x ∈ ys) :
    secGetCodeLabels ⟨n, xs⟩ ⊆ secGetCodeLabels ⟨n, ys⟩ := by
  rintro lab (hl | ⟨n2, ⟨ln, hln, hn2⟩, rfl⟩)
  · exact .inl hl
  · exact .inr ⟨n2, ⟨ln, h ln hln, hn2⟩, rfl⟩

theorem mem_getCodeLabels_of {width : Nat} [NeZero width]
    {secs : List (Section (LabSem.LabLineHOL width))} {sec : Section (LabSem.LabLineHOL width)}
    (hs : sec ∈ secs) {lab : Nat × Nat} (h : lab ∈ secGetCodeLabels sec) :
    lab ∈ getCodeLabels secs := ⟨sec, hs, h⟩

/-- HOL `get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma" (words_as_type_indexed_bitvec)]
theorem getLabelsMapProgToSectionSubsetCodeLabelsLemma {width : Nat} [NeZero width] :
    ∀ p : List (Nat × HolProg width),
      (∀ sec ∈ p.map progToSectionHOL, LabProps.secLabelsOk sec) →
      getLabels (p.map progToSectionHOL) ⊆
        getCodeLabels (p.map progToSectionHOL) ∪
          ⋃₀ (StackProps.getCodeLabels '' {q | q ∈ p.map Prod.snd}) := by
  intro p hok lab ⟨sec, hsec, ln, hln, hlab⟩
  obtain ⟨⟨n, q⟩, hq, rfl⟩ := List.mem_map.mp hsec
  have hok' := hok _ hsec
  rw [progToSection_eq] at hln hok'
  rcases hf : flattenHOL true q n (StackAlloc.nextLab q 2) [] [] with ⟨l, x, y⟩
  rw [hf] at hln hok'
  simp only [List.mem_append, List.mem_singleton] at hln
  rcases hln with hln | rfl
  · have := flattenLabels true q n _ [] [] l x y ⟨hf, fun ln h => hok' ln (by simp [h])⟩
      ⟨_, ⟨ln, hln, rfl⟩, hlab⟩
    rcases this with (h | h) | h
    · simp at h
    · refine .inl (mem_getCodeLabels_of hsec ?_)
      rw [progToSection_eq, hf]
      exact secGetCodeLabels_mono (fun z hz => by simp [hz]) h
    · exact .inr ⟨_, ⟨q, List.mem_map.mpr ⟨_, hq, rfl⟩, rfl⟩, h⟩
  · simp [lineGetLabels] at hlab

/-- HOL `prog_to_section_preserves_MAP_FST` (local). -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "prog_to_section_preserves_MAP_FST" (words_as_type_indexed_bitvec)]
theorem progToSectionPreservesMapFst {width : Nat} [NeZero width] :
    ∀ p : List (Nat × HolProg width),
      (fun n => (n, 0)) '' {n | n ∈ p.map Prod.fst} ⊆ getCodeLabels (p.map progToSectionHOL) := by
  rintro p _ ⟨n, hn, rfl⟩
  obtain ⟨⟨n', q⟩, hq, rfl⟩ := List.mem_map.mp hn
  refine mem_getCodeLabels_of (List.mem_map.mpr ⟨_, hq, rfl⟩) ?_
  rw [progToSection_eq]
  exact .inl rfl

open Classical in
/-- HOL `prog_to_section_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "prog_to_section_labels"
  (words_as_type_indexed_bitvec)]
theorem progToSectionLabels {width : Nat} [NeZero width] {n : Nat} {p : HolProg width}
    {pp : Section (LabSem.LabLineHOL width)} :
    progToSectionHOL (n, p) = pp →
      secGetLabels pp ⊆ secGetCodeLabels pp ∪ complexGetCodeLabels p := by
  rintro rfl lab ⟨ln, hln, hlab⟩
  rw [progToSection_eq] at hln ⊢
  simp only [List.mem_append, List.mem_singleton] at hln
  rcases hln with hln | rfl
  · have := complexFlattenLabels true p n (StackAlloc.nextLab p 2) [] [] ⟨_, ⟨ln, hln, rfl⟩, hlab⟩
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq, List.nil_append,
      List.map_nil, List.not_mem_nil, false_or, Set.mem_image, Set.mem_sUnion] at this
    rcases this with rfl | rfl | ⟨n2, ⟨_, ⟨ln', hl', rfl⟩, hn2⟩, rfl⟩ | h
    · exact .inl (.inl rfl)
    · by_cases hs : ∃ p1 p2, p = .seq p1 p2
      · obtain ⟨a, b, rfl⟩ := hs
        rw [if_pos (show True ∧ ∃ p1 p2 : HolProg width,
          (StackLang.Prog.seq a b : HolProg width) = .seq p1 p2 from ⟨trivial, a, b, rfl⟩)]
        refine .inl (.inr ⟨1, ⟨.label n 1 0, ?_, by simp [lineGetCodeLabels]⟩, rfl⟩)
        rw [flattenHOL]
        simp
      · simp only [true_and, hs, if_false]
        exact .inl (.inl rfl)
    · exact .inl (.inr ⟨n2, ⟨ln', by simp [hl'], hn2⟩, rfl⟩)
    · exact .inr h
  · simp [lineGetLabels] at hlab

/-- HOL `MAP_prog_to_section_preserves_handler_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "MAP_prog_to_section_preserves_handler_labels" (words_as_type_indexed_bitvec)]
theorem mapProgToSectionPreservesHandlerLabels {width : Nat} [NeZero width] :
    ∀ p : List (Nat × HolProg width),
      ⋃₀ {s | s ∈ p.map (fun np => StackProps.stackGetHandlerLabels np.1 np.2)} ⊆
        getCodeLabels (p.map progToSectionHOL) := by
  rintro p lab ⟨_, hs, hlab⟩
  obtain ⟨⟨n, q⟩, hq, rfl⟩ := List.mem_map.mp hs
  refine mem_getCodeLabels_of (List.mem_map.mpr ⟨_, hq, rfl⟩) ?_
  simp only at hlab
  rw [progToSection_eq]
  rcases hf : flattenHOL true q n (StackAlloc.nextLab q 2) [] [] with ⟨l, x, y⟩
  have := flattenPreservesHandlerLabels true q n _ [] [] l x y hf hlab
  simp only
  exact secGetCodeLabels_mono (fun z hz => by simp [hz]) this

/-- HOL `one_prog_section`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "one_prog_section"
  (words_as_type_indexed_bitvec)]
theorem oneProgSection {width : Nat} [NeZero width] {p : List (Nat × HolProg width)} :
    (fun n => (n, 1)) '' {n | n ∈ p.map Prod.fst} ⊆ getCodeLabels (p.map progToSectionHOL) := by
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨⟨n', q⟩, hq, rfl⟩ := List.mem_map.mp hn
  refine mem_getCodeLabels_of (List.mem_map.mpr ⟨_, hq, rfl⟩) ?_
  rw [progToSection_eq]
  by_cases hs : isSeqHOL q = true
  · obtain ⟨a, b, rfl⟩ : ∃ a b, q = .seq a b := by
      cases q <;> simp_all [isSeqHOL]
    refine .inr ⟨1, ⟨.label n' 1 0, ?_, by simp [lineGetCodeLabels]⟩, rfl⟩
    rw [flattenHOL]
    simp
  · refine .inr ⟨1, ⟨.label n' 1 0, ?_, by simp [lineGetCodeLabels]⟩, rfl⟩
    simp [hs]

/-- HOL `get_labels_MAP_prog_to_section_SUBSET_code_labels`. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml"
  "get_labels_MAP_prog_to_section_SUBSET_code_labels" (words_as_type_indexed_bitvec)]
theorem getLabelsMapProgToSectionSubsetCodeLabels {width : Nat} [NeZero width]
    {elabs : Set Nat} :
    ∀ p : List (Nat × HolProg width),
      (∀ sec ∈ p.map progToSectionHOL, LabProps.secLabelsOk sec) ∧
        StackProps.stackGoodCodeLabels p elabs →
      getLabels (p.map progToSectionHOL) ⊆
        getCodeLabels (p.map progToSectionHOL) ∪ (fun n => (n, 0)) '' elabs ∪
          (fun n => (n, 1)) '' elabs := by
  rintro p ⟨hok, hgood⟩ lab hlab
  rcases getLabelsMapProgToSectionSubsetCodeLabelsLemma p hok hlab with h | h
  · exact .inl (.inl h)
  · rcases hgood h with ((((h | h) | h) | h) | h)
    · exact .inl (.inl (mapProgToSectionPreservesHandlerLabels p h))
    · exact .inl (.inl (progToSectionPreservesMapFst p h))
    · exact .inl (.inr h)
    · exact .inl (.inl (oneProgSection h))
    · exact .inr h

end Flapjack.Compiler.Backend.StackToLab.Proofs.LabelSets
