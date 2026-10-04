import Flapjack.Compiler.Backend.WordCopy.Proofs.Invariant
import Flapjack.Pancake.WordConvs
import Flapjack.Pancake.WordConvs.FullInstOkLess
import Flapjack.Pancake.WordConvs.NotCreated
import Flapjack.Pancake.WordConvs.CodeLabels
import Flapjack.Pancake.WordConvs.WfCutsets
import Mathlib.Tactic.Tauto

/-!
# `wordConvsProof` `copy_prop` group

The convention, label, handler and sub-program preservation theorems of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml:1852-2192`. They follow
the output shape `CopyOut` of `copy_prop_prog`: the program structure is kept
and only registers inside leaf statements are renamed (a `Get` may become a
`Move` or `Skip`). The leaf constructors record the copy state used, so a state
invariant can be carried (the `not_alloc_var` invariant for
`pre_alloc_conventions`).
-/

namespace Flapjack.WordConvs

open Flapjack Flapjack.Compiler.Backend.WordCopy Flapjack.Compiler.Encoders.Asm

section Shape

variable {width : Nat} [NeZero width]

/-- The output shape of `copy_prop_prog`, with the copy states of leaf
renamings satisfying `I` (Flapjack infrastructure for the HOL
`copy_prop_prog_ind` proofs). -/
inductive CopyOut (I : CopyState → Prop) :
    WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width) → Prop
  | refl (p) : CopyOut I p p
  | inst (i cs) : I cs → CopyOut I (.inst i) (copyPropInst i cs).1
  | move (pri xs ys) : CopyOut I (.move pri xs) (.move pri ys)
  | ret (v1 v2 cs) : I cs → CopyOut I (.return v1 v2) (.return (lookupEq cs v1) (v2.map (lookupEq cs)))
  | raise (v cs) : I cs → CopyOut I (.raise v) (.raise (lookupEq cs v))
  | opCurrHeap (b dst src cs) : CopyOut I (.opCurrHeap b dst src)
      (.opCurrHeap b dst (if lookupEq cs src = dst then src else lookupEq cs src))
  | set (name n n') : CopyOut I (.set name (.var n)) (.set name (.var n'))
  | getMove (n name ys) : CopyOut I (.get n name) (.move 0 ys)
  | getSkip (n name) : CopyOut I (.get n name) .skip
  | codeBufferWrite (r1 r2 r1' r2') : CopyOut I (.codeBufferWrite r1 r2) (.codeBufferWrite r1' r2')
  | dataBufferWrite (r1 r2 r1' r2') : CopyOut I (.dataBufferWrite r1 r2) (.dataBufferWrite r1' r2')
  | shareInst (op v exp cs) : CopyOut I (.shareInst op v exp) (.shareInst op v (copyPropShare exp cs))
  | seq (a b a' b') : CopyOut I a a' → CopyOut I b b' → CopyOut I (.seq a b) (.seq a' b')
  | ite (cmp r ri r' ri' a b a' b') : CopyOut I a a' → CopyOut I b b' →
      CopyOut I (.ite cmp r ri a b) (.ite cmp r' ri' a' b')
  | mustTerminate (a a') : CopyOut I a a' → CopyOut I (.mustTerminate a) (.mustTerminate a')
  | loop (n a e a') : CopyOut I a a' → CopyOut I (.loop n a e) (.loop n a' e)

/-- Every `copy_prop_prog` output has the `CopyOut` shape, for any state
invariant preserved by `copy_prop_prog` and holding of `empty_eq`. -/
theorem copyPropProg_out (I : CopyState → Prop) (hempty : I emptyEq)
    (hpres : ∀ (p : WordLangProgHOL (BitVec width)) cs, I cs → I (copyPropProg p cs).2) :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : CopyState), I cs → CopyOut I p (copyPropProg p cs).1
  | .skip, _, _ => .refl _
  | .move pri xs, cs, _ => by
      simp only [copyPropProg]
      split
      · exact .move _ _ _
      · exact .refl _
  | .inst i, cs, h => by simp only [copyPropProg]; exact .inst i cs h
  | .return v1 v2, cs, h => by simp only [copyPropProg]; exact .ret v1 v2 cs h
  | .raise v, cs, h => by simp only [copyPropProg]; exact .raise v cs h
  | .opCurrHeap b dst src, cs, _ => by simp only [copyPropProg]; exact .opCurrHeap b dst src cs
  | .tick, _, _ => .refl _
  | .mustTerminate p1, cs, h => by
      simp only [copyPropProg]
      exact .mustTerminate _ _ (copyPropProg_out I hempty hpres p1 cs h)
  | .seq p1 p2, cs, h => by
      simp only [copyPropProg]
      exact .seq _ _ _ _ (copyPropProg_out I hempty hpres p1 cs h)
        (copyPropProg_out I hempty hpres p2 _ (hpres p1 cs h))
  | .ite cmp r ri p1 p2, cs, h => by
      simp only [copyPropProg]
      exact .ite _ _ _ _ _ _ _ _ _ (copyPropProg_out I hempty hpres p1 cs h)
        (copyPropProg_out I hempty hpres p2 cs h)
  | .set name exp, cs, _ => by
      simp only [copyPropProg]
      split
      · exact .set _ _ _
      · exact .refl _
  | .get n name, cs, _ => by
      simp only [copyPropProg]
      split
      · exact .refl _
      · split
        · exact .getMove _ _ _
        · exact .getSkip _ _
  | .call _ _ _ _, _, _ => by simp only [copyPropProg]; exact .refl _
  | .alloc _ _, _, _ => by simp only [copyPropProg]; exact .refl _
  | .storeConsts _ _ _ _ _, _, _ => by simp only [copyPropProg]; exact .refl _
  | .locValue _ _, _, _ => by simp only [copyPropProg]; exact .refl _
  | .install _ _ _ _ _, _, _ => by simp only [copyPropProg]; exact .refl _
  | .codeBufferWrite r1 r2, cs, _ => by simp only [copyPropProg]; exact .codeBufferWrite _ _ _ _
  | .dataBufferWrite r1 r2, cs, _ => by simp only [copyPropProg]; exact .dataBufferWrite _ _ _ _
  | .ffi _ _ _ _ _ _, _, _ => by simp only [copyPropProg]; exact .refl _
  | .shareInst op v exp, cs, _ => by simp only [copyPropProg]; exact .shareInst op v exp cs
  | .loop names c exitNames, _, _ => by
      simp only [copyPropProg]
      exact .loop _ _ _ _ (copyPropProg_out I hempty hpres c emptyEq hempty)
  | .break _, _, _ => .refl _
  | .continue _, _, _ => .refl _
  | .assign _ _, _, _ => by simp only [copyPropProg]; exact .refl _
  | .store _ _, _, _ => by simp only [copyPropProg]; exact .refl _

theorem copyProp_out (p : WordLangProgHOL (BitVec width)) :
    CopyOut (fun _ => True) p (copyProp p) :=
  copyPropProg_out _ trivial (fun _ _ _ => trivial) p emptyEq trivial

theorem CopyOut.mono {I J : CopyState → Prop} (hIJ : ∀ cs, I cs → J cs)
    {p q : WordLangProgHOL (BitVec width)} (h : CopyOut I p q) : CopyOut J p q := by
  induction h with
  | refl => exact .refl _
  | inst i cs hc => exact .inst i cs (hIJ cs hc)
  | move => exact .move _ _ _
  | ret v1 v2 cs hc => exact .ret v1 v2 cs (hIJ cs hc)
  | raise v cs hc => exact .raise v cs (hIJ cs hc)
  | opCurrHeap => exact .opCurrHeap _ _ _ _
  | set => exact .set _ _ _
  | getMove => exact .getMove _ _ _
  | getSkip => exact .getSkip _ _
  | codeBufferWrite => exact .codeBufferWrite _ _ _ _
  | dataBufferWrite => exact .dataBufferWrite _ _ _ _
  | shareInst => exact .shareInst _ _ _ _
  | seq _ _ _ _ _ _ iha ihb => exact .seq _ _ _ _ iha ihb
  | ite _ _ _ _ _ _ _ _ _ _ _ iha ihb => exact .ite _ _ _ _ _ _ _ _ _ iha ihb
  | mustTerminate _ _ _ ih => exact .mustTerminate _ _ ih
  | loop _ _ _ _ _ ih => exact .loop _ _ _ _ ih

/-- `copy_prop_inst` returns `Skip` or an instruction. -/
theorem copyPropInst_shape (i : WordLangInst (BitVec width)) (cs : CopyState) :
    (copyPropInst i cs).1 = .skip ∨ ∃ j, (copyPropInst i cs).1 = .inst j := by
  rcases i with _ | _ | a | ⟨op, r, ad⟩ | f
  · simp [copyPropInst]
  · simp [copyPropInst]
  · cases a <;> simp [copyPropInst]
  · cases op <;> cases ad <;> simp [copyPropInst]
  · cases f <;> simp only [copyPropInst] <;> (try split) <;> simp

theorem wfCutsets_copyOut {I : CopyState → Prop} {p q : WordLangProgHOL (BitVec width)}
    (h : CopyOut I p q) (hp : wfCutsets p) : wfCutsets q := by
  induction h with
  | refl => exact hp
  | inst i cs =>
    rcases copyPropInst_shape i cs with h | ⟨j, h⟩ <;> rw [h] <;> simp [wfCutsets]
  | seq _ _ _ _ _ _ iha ihb => simp only [wfCutsets] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ _ _ iha ihb => simp only [wfCutsets] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih => simp only [wfCutsets] at hp ⊢; exact ih hp
  | loop _ _ _ _ _ ih => simp only [wfCutsets] at hp ⊢; exact ⟨hp.1, hp.2.1, ih hp.2.2⟩
  | _ => simp [wfCutsets]

theorem extractLabels_copyOut {I : CopyState → Prop} {p q : WordLangProgHOL (BitVec width)}
    (h : CopyOut I p q) : extractLabels q = extractLabels p := by
  induction h with
  | refl => rfl
  | inst i cs =>
    rcases copyPropInst_shape i cs with h | ⟨j, h⟩ <;> rw [h] <;> simp [extractLabels]
  | seq _ _ _ _ _ _ iha ihb => simp [extractLabels, iha, ihb]
  | ite _ _ _ _ _ _ _ _ _ _ _ iha ihb => simp [extractLabels, iha, ihb]
  | mustTerminate _ _ _ ih => simp [extractLabels, ih]
  | loop _ _ _ _ _ ih => simp [extractLabels, ih]
  | _ => simp [extractLabels]

theorem getCodeLabels_copyOut {I : CopyState → Prop} {p q : WordLangProgHOL (BitVec width)}
    (h : CopyOut I p q) : getCodeLabelsHOL q = getCodeLabelsHOL p := by
  induction h with
  | refl => rfl
  | inst i cs =>
    rcases copyPropInst_shape i cs with h | ⟨j, h⟩ <;> rw [h] <;> simp [getCodeLabelsHOL]
  | seq _ _ _ _ _ _ iha ihb => simp [getCodeLabelsHOL, iha, ihb]
  | ite _ _ _ _ _ _ _ _ _ _ _ iha ihb => simp [getCodeLabelsHOL, iha, ihb]
  | mustTerminate _ _ _ ih => simp [getCodeLabelsHOL, ih]
  | loop _ _ _ _ _ ih => simp [getCodeLabelsHOL, ih]
  | _ => simp [getCodeLabelsHOL]

theorem goodHandlers_copyOut (n : Nat) {I : CopyState → Prop} {p q : WordLangProgHOL (BitVec width)}
    (h : CopyOut I p q) : goodHandlersHOL n q = goodHandlersHOL n p := by
  induction h with
  | refl => rfl
  | inst i cs =>
    rcases copyPropInst_shape i cs with h | ⟨j, h⟩ <;> rw [h] <;> simp [goodHandlersHOL]
  | seq _ _ _ _ _ _ iha ihb => simp [goodHandlersHOL, iha, ihb]
  | ite _ _ _ _ _ _ _ _ _ _ _ iha ihb => simp [goodHandlersHOL, iha, ihb]
  | mustTerminate _ _ _ ih => simp [goodHandlersHOL, ih]
  | loop _ _ _ _ _ ih => simp [goodHandlersHOL, ih]
  | _ => simp [goodHandlersHOL]

theorem notCreatedSubprogs_copyOut (P : WordLangProgHOL (BitVec width) → Bool)
    {I : CopyState → Prop} {p q : WordLangProgHOL (BitVec width)} (h : CopyOut I p q)
    (hp : notCreatedSubprogsHOL P p = true) : notCreatedSubprogsHOL P q = true := by
  induction h with
  | refl => exact hp
  | inst i cs =>
    rcases copyPropInst_shape i cs with h | ⟨j, h⟩ <;> rw [h] <;> simp [notCreatedSubprogsHOL]
  | shareInst => simpa [notCreatedSubprogsHOL] using hp
  | seq _ _ _ _ _ _ iha ihb =>
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih =>
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at hp ⊢; exact ⟨hp.1, ih hp.2⟩
  | loop _ _ _ _ _ ih => simp only [notCreatedSubprogsHOL] at hp ⊢; exact ih hp
  | _ => simp [notCreatedSubprogsHOL]

theorem flatExp_copyPropShare (exp : WordLangExpHOL (BitVec width)) (cs : CopyState) (op : WordMemOp)
    (v : Nat) (hp : flatExpConventions (.shareInst op v exp) = true) :
    flatExpConventions (.shareInst op v (copyPropShare exp cs)) = true := by
  unfold copyPropShare
  split <;> simp_all [flatExpConventions]

theorem flatExpConventions_copyOut {I : CopyState → Prop} {p q : WordLangProgHOL (BitVec width)}
    (h : CopyOut I p q) (hp : flatExpConventions p = true) : flatExpConventions q = true := by
  induction h with
  | refl => exact hp
  | inst i cs =>
    rcases copyPropInst_shape i cs with h | ⟨j, h⟩ <;> rw [h] <;> simp [flatExpConventions]
  | shareInst op v exp cs => exact flatExp_copyPropShare exp cs op v hp
  | seq _ _ _ _ _ _ iha ihb =>
    simp only [flatExpConventions, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [flatExpConventions, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih => simp only [flatExpConventions] at hp ⊢; exact ih hp
  | loop _ _ _ _ _ ih => simp only [flatExpConventions] at hp ⊢; exact ih hp
  | _ => simp [flatExpConventions]

theorem distinctTarReg_copyPropInst (i : WordLangInst (BitVec width)) (cs : CopyState)
    (hp : distinctTarRegExact (HolInst.ofWordLangInst i) = true) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) (copyPropInst i cs).1 = true := by
  rcases i with _ | _ | a | ⟨op, r, ad⟩ | f
  · simp [copyPropInst, everyInst]
  · simp [copyPropInst, everyInst, HolInst.ofWordLangInst, distinctTarRegExact]
  · cases a <;> simp only [copyPropInst, everyInst, HolInst.ofWordLangInst, HolArith.ofWordLangArith,
      distinctTarRegExact] at hp ⊢ <;> (repeat' split) <;>
      simp_all [HolRegImm.ofWordRegImm, lookupEqImm] <;> (repeat' split at *) <;> (try split_ifs at *) <;> (try simp_all) <;>
      exact fun h => absurd h.symm ‹_›
  · cases op <;> cases ad <;> simp [copyPropInst, everyInst, HolInst.ofWordLangInst, distinctTarRegExact]
  · cases f <;> simp only [copyPropInst] <;> (try split) <;>
      simp [everyInst, HolInst.ofWordLangInst, distinctTarRegExact]

theorem distinctTarReg_copyOut {I : CopyState → Prop} {p q : WordLangProgHOL (BitVec width)}
    (h : CopyOut I p q)
    (hp : everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) p = true) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) q = true := by
  induction h with
  | refl => exact hp
  | inst i cs => exact distinctTarReg_copyPropInst i cs hp
  | opCurrHeap b dst src cs =>
    simp only [everyInst, HolInst.ofWordLangInst, HolArith.ofWordLangArith, distinctTarRegExact,
      HolRegImm.ofWordRegImm] at hp ⊢
    split <;> simp_all
  | seq _ _ _ _ _ _ iha ihb =>
    simp only [everyInst, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [everyInst, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih => simp only [everyInst] at hp ⊢; exact ih hp
  | loop _ _ _ _ _ ih => simp only [everyInst] at hp ⊢; exact ih hp
  | _ => simp [everyInst]

theorem fullInstOkLess_copyPropInst (c : AsmConfigExact width) (i : WordLangInst (BitVec width))
    (cs : CopyState) (hp : fullInstOkLessExact c (.inst i) = true) :
    fullInstOkLessExact c (copyPropInst i cs).1 = true := by
  simp only [fullInstOkLessExact, fullInstOkLessWith] at hp ⊢
  rcases i with _ | _ | a | ⟨op, r, ad⟩ | f
  · simp [copyPropInst, fullInstOkLessWith]
  · simpa [copyPropInst, fullInstOkLessWith] using hp
  · cases a with
    | binop bop r1 r2 ri =>
      cases ri <;> simp only [copyPropInst, lookupEqImm] <;> (try split_ifs) <;>
        simp_all [fullInstOkLessWith, HolInst.ofWordLangInst, HolArith.ofWordLangArith,
          HolRegImm.ofWordRegImm, instOkLessExact]
    | shift sh r1 r2 ri =>
      cases ri <;> simp only [copyPropInst, lookupEqImm] <;> (try split_ifs) <;>
        simp_all [fullInstOkLessWith, HolInst.ofWordLangInst, HolArith.ofWordLangArith,
          HolRegImm.ofWordRegImm, instOkLessExact]
    | addCarry r1 r2 r3 r4 =>
      simp only [copyPropInst]
      split_ifs <;> simp_all [fullInstOkLessWith, HolInst.ofWordLangInst, HolArith.ofWordLangArith,
          instOkLessExact, @eq_comm _ r1]
      tauto
    | addOverflow r1 r2 r3 r4 =>
      simp only [copyPropInst]
      split_ifs <;> simp_all [fullInstOkLessWith, HolInst.ofWordLangInst, HolArith.ofWordLangArith,
          instOkLessExact, @eq_comm _ r1]
    | subOverflow r1 r2 r3 r4 =>
      simp only [copyPropInst]
      split_ifs <;> simp_all [fullInstOkLessWith, HolInst.ofWordLangInst, HolArith.ofWordLangArith,
          instOkLessExact, @eq_comm _ r1]
    | _ =>
      simpa [copyPropInst, fullInstOkLessWith, HolInst.ofWordLangInst, HolArith.ofWordLangArith,
        instOkLessExact] using hp
  · cases op <;> cases ad <;> simpa [copyPropInst, fullInstOkLessWith, HolInst.ofWordLangInst,
      HolAddr.ofWordLangAddr, instOkLessExact] using hp
  · cases f <;> simp only [copyPropInst] at hp ⊢ <;> (try split) <;>
      simp_all [fullInstOkLessWith, HolInst.ofWordLangInst, instOkLessExact]

/-- `copy_prop_share` renames only the base register of the address. -/
theorem expToAddr_copyPropShare (exp : WordLangExpHOL (BitVec width)) (cs : CopyState) :
    expToAddrHOL (copyPropShare exp cs) =
      (expToAddrHOL exp).map (fun a => match a with | .addr b o => .addr (lookupEq cs b) o) := by
  unfold copyPropShare
  split
  · simp [expToAddrHOL]
  · simp [expToAddrHOL]
  · rename_i h1 h2
    unfold expToAddrHOL
    split <;> simp_all

theorem fullInstOkLess_copyOut (c : AsmConfigExact width) {I : CopyState → Prop}
    {p q : WordLangProgHOL (BitVec width)} (h : CopyOut I p q)
    (hp : fullInstOkLessExact c p = true) : fullInstOkLessExact c q = true := by
  induction h with
  | refl => exact hp
  | inst i cs => exact fullInstOkLess_copyPropInst c i cs hp
  | shareInst op v exp cs =>
    simp only [fullInstOkLessExact, fullInstOkLessWith, expToAddr_copyPropShare] at hp ⊢
    cases h : expToAddrHOL exp with
    | none => simp [h] at hp
    | some a => cases a; simpa [h] using hp
  | seq _ _ _ _ _ _ iha ihb =>
    simp only [fullInstOkLessExact, fullInstOkLessWith, Bool.and_eq_true] at hp iha ihb ⊢
    exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [fullInstOkLessExact, fullInstOkLessWith, Bool.and_eq_true] at hp iha ihb ⊢
    exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih =>
    simp only [fullInstOkLessExact, fullInstOkLessWith] at hp ih ⊢; exact ih hp
  | loop _ _ _ _ _ ih =>
    simp only [fullInstOkLessExact, fullInstOkLessWith] at hp ih ⊢; exact ih hp
  | _ => simp [fullInstOkLessExact, fullInstOkLessWith]

/-- The `not_alloc_var` state invariant of `copy_prop_prog_not_alloc_var`
(Flapjack infrastructure naming HOL's inline hypothesis). -/
def NotAllocInv (cs : CopyState) : Prop :=
  ∀ x, ¬isAllocVar x = true → sptLookup x cs.toEq = none

theorem notAllocInv_emptyEq : NotAllocInv emptyEq := fun _ _ => by simp [emptyEq]

theorem notAllocInv_removeEq {cs : CopyState} (y : Nat) (h : NotAllocInv cs) :
    NotAllocInv (removeEq cs y) := by
  unfold removeEq; split
  · exact h
  · exact notAllocInv_emptyEq

theorem notAllocInv_removeEqs : ∀ (yy : List Nat) {cs : CopyState}, NotAllocInv cs →
    NotAllocInv (removeEqs cs yy)
  | [], _, h => h
  | y :: yy, _, h => notAllocInv_removeEqs yy (notAllocInv_removeEq y h)

theorem notAllocInv_setEq {cs : CopyState} (x y : Nat) (h : NotAllocInv cs) :
    NotAllocInv (setEq cs x y) := by
  intro v hv
  rw [setEq_eq]
  split
  · rename_i hxy
    have hx : v ≠ x := fun e => hv (e ▸ hxy.1)
    have hy : v ≠ y := fun e => hv (e ▸ hxy.2)
    split <;> simp only [sptLookupInsert, if_neg hx, if_neg hy] <;> exact h v hv
  · exact h v hv

theorem notAllocInv_setStoreEq {cs : CopyState} (name : WordStoreHOL) (y : Nat) (h : NotAllocInv cs) :
    NotAllocInv (setStoreEq cs name y) := by
  intro v hv
  rw [setStoreEq_eq]
  split
  · rename_i hy
    have hy' : v ≠ y := fun e => hv (e ▸ hy)
    split
    · simp only [sptLookupInsert, if_neg hy']; exact h v hv
    · exact h v hv
  · exact notAllocInv_emptyEq v hv

theorem notAllocInv_copyPropMove : ∀ (xs : List (Nat × Nat)) {cs : CopyState}, NotAllocInv cs →
    NotAllocInv (copyPropMove xs cs).2
  | [], _, h => h
  | (x, y) :: xs, cs, h => by
      simp only [copyPropMove]
      exact notAllocInv_setEq x y (notAllocInv_removeEq x (notAllocInv_copyPropMove xs h))

theorem notAllocInv_copyPropInst (i : WordLangInst (BitVec width)) {cs : CopyState}
    (h : NotAllocInv cs) : NotAllocInv (copyPropInst i cs).2 := by
  rcases i with _ | _ | a | ⟨op, r, ad⟩ | f
  · exact h
  · exact notAllocInv_removeEq _ h
  · cases a <;> simp only [copyPropInst] <;>
      first | exact notAllocInv_removeEq _ h | exact notAllocInv_removeEqs _ h
  · cases op <;> cases ad <;> simp only [copyPropInst] <;>
      first | exact h | exact notAllocInv_removeEq _ h
  · cases f <;> simp only [copyPropInst] <;>
      first | exact h | exact notAllocInv_removeEq _ h | exact notAllocInv_removeEqs _ h

theorem notAllocInv_mergeEqs {cs ds : CopyState} (h : NotAllocInv cs) : NotAllocInv (mergeEqs cs ds) := by
  intro v hv
  simp only [mergeEqs, sptLookupInterEq, h v hv]

theorem lookupEq_notAlloc {cs : CopyState} (h : NotAllocInv cs) {v : Nat} (hv : ¬isAllocVar v = true) :
    lookupEq cs v = v := by
  simp [lookupEq, h v hv]

theorem notAllocVar_even {v : Nat} (h : v % 2 = 0) : ¬isAllocVar v = true := by
  simp only [isAllocVar, decide_eq_true_eq]; omega

theorem everyStackVar_copyOut (P : Nat → Bool) {I : CopyState → Prop}
    {p q : WordLangProgHOL (BitVec width)} (h : CopyOut I p q)
    (hp : everyStackVarHOL P p = true) : everyStackVarHOL P q = true := by
  induction h with
  | refl => exact hp
  | inst i cs =>
    rcases copyPropInst_shape i cs with h | ⟨j, h⟩ <;> rw [h] <;> simp [everyStackVarHOL]
  | seq _ _ _ _ _ _ iha ihb =>
    simp only [everyStackVarHOL, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [everyStackVarHOL, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih => simp only [everyStackVarHOL] at hp ⊢; exact ih hp
  | loop _ _ _ _ _ ih => simp only [everyStackVarHOL] at hp ⊢; exact ih hp
  | _ => simp [everyStackVarHOL]

theorem callArg_copyPropInst (i : WordLangInst (BitVec width)) {cs : CopyState} (hI : NotAllocInv cs)
    (hp : callArgConventionHOL (.inst i : WordLangProgHOL (BitVec width)) = true) :
    callArgConventionHOL (copyPropInst i cs).1 = true := by
  have l8 := lookupEq_notAlloc hI (v := 8) (notAllocVar_even rfl)
  have l6 := lookupEq_notAlloc hI (v := 6) (notAllocVar_even rfl)
  have l0 := lookupEq_notAlloc hI (v := 0) (notAllocVar_even rfl)
  simp only [callArgConventionHOL] at hp
  rcases i with _ | _ | a | ⟨op, r, ad⟩ | f
  · simp [copyPropInst, callArgConventionHOL]
  · simp [copyPropInst, callArgConventionHOL, instArgConvention]
  · cases a with
    | shift sh r1 r2 ri =>
      cases ri with
      | reg r =>
        simp only [instArgConvention, beq_iff_eq] at hp
        subst hp
        simp only [copyPropInst, lookupEqImm, l8]
        split_ifs <;> simp [callArgConventionHOL, instArgConvention]
      | imm w =>
        simp only [copyPropInst, lookupEqImm]
        split_ifs <;> simp [callArgConventionHOL, instArgConvention]
    | longDiv r1 r2 r3 r4 r5 =>
      simp only [instArgConvention, Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hp
      simp [copyPropInst, callArgConventionHOL, instArgConvention, l6, l0]
    | binop bop r1 r2 ri =>
      simp only [copyPropInst]
      split_ifs <;> simp [callArgConventionHOL, instArgConvention]
    | _ =>
      simp only [copyPropInst]
      (try split_ifs) <;> simp_all [callArgConventionHOL, instArgConvention]
  · cases op <;> cases ad <;> simp [copyPropInst, callArgConventionHOL, instArgConvention]
  · cases f <;> simp only [copyPropInst] <;> (try split) <;>
      simp [callArgConventionHOL, instArgConvention]

theorem callArg_copyOut {p q : WordLangProgHOL (BitVec width)} (h : CopyOut NotAllocInv p q)
    (hp : callArgConventionHOL p = true) : callArgConventionHOL q = true := by
  induction h with
  | refl => exact hp
  | inst i cs hc => exact callArg_copyPropInst i hc hp
  | ret v1 v2 cs hc =>
    simp only [callArgConventionHOL, beq_iff_eq] at hp ⊢
    have : v2.map (lookupEq cs) = v2 := by
      conv_rhs => rw [← List.map_id v2]
      refine List.map_congr_left (fun v hv => ?_)
      rw [hp] at hv
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hv
      exact lookupEq_notAlloc hc (notAllocVar_even (by omega))
    rw [this]; exact hp
  | raise v cs hc =>
    simp only [callArgConventionHOL, beq_iff_eq] at hp ⊢
    subst hp; exact lookupEq_notAlloc hc (notAllocVar_even rfl)
  | seq _ _ _ _ _ _ iha ihb =>
    simp only [callArgConventionHOL, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | ite _ _ _ _ _ _ _ _ _ _ _ iha ihb =>
    simp only [callArgConventionHOL, Bool.and_eq_true] at hp ⊢; exact ⟨iha hp.1, ihb hp.2⟩
  | mustTerminate _ _ _ ih => simp only [callArgConventionHOL] at hp ⊢; exact ih hp
  | loop _ _ _ _ _ ih => simp only [callArgConventionHOL] at hp ⊢; exact ih hp
  | _ => simp [callArgConventionHOL]

theorem notAllocInv_copyPropProg :
    ∀ (p : WordLangProgHOL (BitVec width)) {cs : CopyState}, NotAllocInv cs →
      NotAllocInv (copyPropProg p cs).2
  | .move pri xs, cs, h => by
      simp only [copyPropProg]
      split
      · exact notAllocInv_copyPropMove xs h
      · exact notAllocInv_emptyEq
  | .inst i, _, h => by simp only [copyPropProg]; exact notAllocInv_copyPropInst i h
  | .opCurrHeap _ dst _, _, h => by simp only [copyPropProg]; exact notAllocInv_removeEq dst h
  | .mustTerminate p1, cs, h => by simp only [copyPropProg]; exact notAllocInv_copyPropProg p1 h
  | .seq p1 p2, cs, h => by
      simp only [copyPropProg]
      exact notAllocInv_copyPropProg p2 (notAllocInv_copyPropProg p1 h)
  | .ite _ _ _ p1 p2, cs, h => by
      simp only [copyPropProg]
      exact notAllocInv_mergeEqs (notAllocInv_copyPropProg p1 h)
  | .set name exp, cs, h => by
      simp only [copyPropProg]
      split
      · exact notAllocInv_setStoreEq _ _ h
      · exact notAllocInv_emptyEq
  | .get n name, cs, h => by
      simp only [copyPropProg]
      split
      · exact notAllocInv_setStoreEq _ _ (notAllocInv_removeEq _ h)
      · split
        · exact notAllocInv_copyPropMove _ h
        · exact h
  | .storeConsts _ _ _ _ _, _, h => by simp only [copyPropProg]; exact notAllocInv_removeEqs _ h
  | .locValue r _, _, h => by simp only [copyPropProg]; exact notAllocInv_removeEq r h
  | .shareInst _ v _, _, h => by simp only [copyPropProg]; exact notAllocInv_removeEq v h
  | .skip, _, h | .tick, _, h | .break _, _, h | .continue _, _, h
  | .return _ _, _, h | .raise _, _, h
  | .codeBufferWrite _ _, _, h | .dataBufferWrite _ _, _, h => by simp only [copyPropProg]; exact h
  | .call _ _ _ _, _, _ | .alloc _ _, _, _ | .install _ _ _ _ _, _, _ | .ffi _ _ _ _ _ _, _, _
  | .loop _ _ _, _, _ | .assign _ _, _, _ | .store _ _, _, _ => by
      simp only [copyPropProg]; exact notAllocInv_emptyEq

end Shape

/-- HOL `wf_cutsets_copy_prop_aux` (`wordConvsProofScript.sml:1873-1878`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "wf_cutsets_copy_prop_aux" (words_as_type_indexed_bitvec)]
theorem wf_cutsets_copy_prop_aux {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : CopyState),
      wfCutsets p → wfCutsets (copyPropProg p cs).1 :=
  fun p cs => wfCutsets_copyOut (copyPropProg_out (fun _ => True) trivial (fun _ _ _ => trivial) p cs trivial)

/-- HOL `wf_cutsets_copy_prop` (`wordConvsProofScript.sml:1880-1884`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "wf_cutsets_copy_prop" (words_as_type_indexed_bitvec)]
theorem wf_cutsets_copy_prop {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width)) :
    wfCutsets p → wfCutsets (copyProp p) :=
  wf_cutsets_copy_prop_aux p emptyEq

/-- HOL `every_inst_distinct_tar_reg_copy_prop_aux` (`wordConvsProofScript.sml:1886-1907`);
HOL's `every_inst distinct_tar_reg` over `'a inst` reads each instruction through the
reviewed `HolInst.ofWordLangInst` mirror. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_distinct_tar_reg_copy_prop_aux" (words_as_type_indexed_bitvec)]
theorem every_inst_distinct_tar_reg_copy_prop_aux {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : CopyState),
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) p = true →
      everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) (copyPropProg p cs).1 = true :=
  fun p cs => distinctTarReg_copyOut
    (copyPropProg_out (fun _ => True) trivial (fun _ _ _ => trivial) p cs trivial)

/-- HOL `every_inst_distinct_tar_reg_copy_prop` (`wordConvsProofScript.sml:1909-1914`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "every_inst_distinct_tar_reg_copy_prop" (words_as_type_indexed_bitvec)]
theorem every_inst_distinct_tar_reg_copy_prop {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) :
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) p = true →
    everyInst (fun i => distinctTarRegExact (HolInst.ofWordLangInst i)) (copyProp p) = true :=
  every_inst_distinct_tar_reg_copy_prop_aux p emptyEq

/-- HOL `extract_labels_copy_prop_aux` (`wordConvsProofScript.sml:1916-1922`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_copy_prop_aux" (words_as_type_indexed_bitvec)]
theorem extract_labels_copy_prop_aux {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : CopyState),
      extractLabels (copyPropProg p cs).1 = extractLabels p :=
  fun p cs => extractLabels_copyOut
    (copyPropProg_out (fun _ => True) trivial (fun _ _ _ => trivial) p cs trivial)

/-- HOL `extract_labels_copy_prop` (`wordConvsProofScript.sml:1924-1929`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "extract_labels_copy_prop" (words_as_type_indexed_bitvec)]
theorem extract_labels_copy_prop {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width)) :
    extractLabels (copyProp p) = extractLabels p :=
  extract_labels_copy_prop_aux p emptyEq

/-- HOL `flat_exp_conventions_copy_prop_aux` (`wordConvsProofScript.sml:1931-1940`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "flat_exp_conventions_copy_prop_aux" (words_as_type_indexed_bitvec)]
theorem flat_exp_conventions_copy_prop_aux {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : CopyState),
      flatExpConventions p = true → flatExpConventions (copyPropProg p cs).1 = true :=
  fun p cs => flatExpConventions_copyOut
    (copyPropProg_out (fun _ => True) trivial (fun _ _ _ => trivial) p cs trivial)

/-- HOL `flat_exp_conventions_copy_prop` (`wordConvsProofScript.sml:1942-1947`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "flat_exp_conventions_copy_prop" (words_as_type_indexed_bitvec)]
theorem flat_exp_conventions_copy_prop {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) :
    flatExpConventions p = true → flatExpConventions (copyProp p) = true :=
  flat_exp_conventions_copy_prop_aux p emptyEq

/-- HOL `copy_prop_prog_not_alloc_var_aux1` (`wordConvsProofScript.sml:1949-1955`). The
inner `∀x` of the hypothesis shadows the free `x`, as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "copy_prop_prog_not_alloc_var_aux1"]
theorem copy_prop_prog_not_alloc_var_aux1 (cs : CopyState) (x y : Nat) :
    (∀ x, ¬isAllocVar x = true → sptLookup x cs.toEq = none) →
    ¬isAllocVar x = true → sptLookup x (removeEq cs y).toEq = none :=
  fun h hx => notAllocInv_removeEq y h x hx

/-- HOL `copy_prop_prog_not_alloc_var_aux2` (`wordConvsProofScript.sml:1957-1965`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "copy_prop_prog_not_alloc_var_aux2"]
theorem copy_prop_prog_not_alloc_var_aux2 (x : Nat) (yy : List Nat) :
    ∀ cs : CopyState, (∀ x, ¬isAllocVar x = true → sptLookup x cs.toEq = none) →
      ¬isAllocVar x = true → sptLookup x (removeEqs cs yy).toEq = none :=
  fun _ h hx => notAllocInv_removeEqs yy h x hx

/-- HOL `copy_prop_prog_not_alloc_var` (`wordConvsProofScript.sml:1968-2032`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "copy_prop_prog_not_alloc_var" (words_as_type_indexed_bitvec)]
theorem copy_prop_prog_not_alloc_var {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : CopyState),
      (∀ x, ¬isAllocVar x = true → sptLookup x cs.toEq = none) →
      ∀ x, ¬isAllocVar x = true → sptLookup x (copyPropProg p cs).2.toEq = none :=
  fun p _ h => notAllocInv_copyPropProg p h

/-- HOL `pre_alloc_conventions_copy_prop_aux` (`wordConvsProofScript.sml:2034-2082`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "pre_alloc_conventions_copy_prop_aux" (words_as_type_indexed_bitvec)]
theorem pre_alloc_conventions_copy_prop_aux {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : CopyState),
      (∀ x, ¬isAllocVar x = true → sptLookup x cs.toEq = none) →
      preAllocConventionsHOL p = true → preAllocConventionsHOL (copyPropProg p cs).1 = true := by
  intro p cs h hp
  have hout := copyPropProg_out NotAllocInv notAllocInv_emptyEq
    (fun p _ h => notAllocInv_copyPropProg p h) p cs h
  simp only [preAllocConventionsHOL, Bool.and_eq_true] at hp ⊢
  exact ⟨everyStackVar_copyOut _ hout hp.1, callArg_copyOut hout hp.2⟩

/-- HOL `pre_alloc_conventions_copy_prop` (`wordConvsProofScript.sml:2084-2090`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "pre_alloc_conventions_copy_prop" (words_as_type_indexed_bitvec)]
theorem pre_alloc_conventions_copy_prop {width : Nat} [NeZero width]
    (p : WordLangProgHOL (BitVec width)) :
    preAllocConventionsHOL p = true → preAllocConventionsHOL (copyProp p) = true :=
  pre_alloc_conventions_copy_prop_aux p emptyEq notAllocInv_emptyEq

/-- HOL `full_inst_ok_less_copy_prop_aux` (`wordConvsProofScript.sml:2092-2129`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "full_inst_ok_less_copy_prop_aux" (words_as_type_indexed_bitvec)]
theorem full_inst_ok_less_copy_prop_aux {width : Nat} [NeZero width] (ac : AsmConfigExact width) :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : CopyState),
      fullInstOkLessExact ac p = true → fullInstOkLessExact ac (copyPropProg p cs).1 = true :=
  fun p cs => fullInstOkLess_copyOut ac
    (copyPropProg_out (fun _ => True) trivial (fun _ _ _ => trivial) p cs trivial)

/-- HOL `full_inst_ok_less_copy_prop` (`wordConvsProofScript.sml:2131-2136`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "full_inst_ok_less_copy_prop" (words_as_type_indexed_bitvec)]
theorem full_inst_ok_less_copy_prop {width : Nat} [NeZero width] (ac : AsmConfigExact width)
    (p : WordLangProgHOL (BitVec width)) :
    fullInstOkLessExact ac p = true → fullInstOkLessExact ac (copyProp p) = true :=
  full_inst_ok_less_copy_prop_aux ac p emptyEq

/-- HOL `word_get_code_labels_copy_prop` (`wordConvsProofScript.sml:2138-2155`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_get_code_labels_copy_prop" (words_as_type_indexed_bitvec)]
theorem word_get_code_labels_copy_prop {width : Nat} [NeZero width]
    (ps : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (copyProp ps) = getCodeLabelsHOL ps :=
  getCodeLabels_copyOut (copyProp_out ps)

/-- HOL `word_good_handlers_copy_prop` (`wordConvsProofScript.sml:2157-2174`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "word_good_handlers_copy_prop" (words_as_type_indexed_bitvec)]
theorem word_good_handlers_copy_prop {width : Nat} [NeZero width] (n : Nat)
    (ps : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n (copyProp ps) = true ↔ goodHandlersHOL n ps = true := by
  rw [goodHandlers_copyOut n (copyProp_out ps)]

/-- HOL `copy_prop_not_created_subprogs` (`wordConvsProofScript.sml:2176-2192`); HOL's free
predicate `P` is the leading binder. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "copy_prop_not_created_subprogs" (words_as_type_indexed_bitvec)]
theorem copy_prop_not_created_subprogs {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) (prog : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P prog = true → notCreatedSubprogsHOL P (copyProp prog) = true :=
  notCreatedSubprogs_copyOut P (copyProp_out prog)

end Flapjack.WordConvs
