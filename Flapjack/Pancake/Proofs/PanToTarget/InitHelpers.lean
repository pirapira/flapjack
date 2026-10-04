import Flapjack.Pancake.Proofs.PanToTarget
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileKeys
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
import Flapjack.Compiler.Backend.StackProps.EvaluateConsts
import Flapjack.Misc.GoodDimindex
import Flapjack.Misc.Alignment
import Flapjack.Pancake.CrepToLoop
import Flapjack.Compiler.Backend.BvlToBvi
import Flapjack.FiniteMap.MapKeys
import Flapjack.Misc.PredSet

/-!
# `pan_to_targetProof`: arithmetic and initialization helpers

Helper theorems of `cakeml/pancake/proofs/pan_to_targetProofScript.sml` used by
`pan_to_target_compile_semantics`: `word_to_stack_compile_FST` (79-87),
`good_dimindex_0w_8w` (249-256), `full_make_init_be` (277-288), `n2w_sub_alt`
(1193-1201), `aligned_n2w_IMP` (1203-1209), `good_dimindex_div_mul` (1242-1248) and
`InitGlobals_location_eq_first_name` (1250-1254). HOL's `≤` on words is the signed
`word_le`, rendered by `BitVec.sle`.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack Flapjack.Compiler.Encoders.Asm

namespace InitHelpersCarrier

/-- Same-module canonical finite-support witness for the `regs`/`fpRegs`/`store`
    fields named by `full_make_init_be`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

end InitHelpersCarrier

/-- HOL `word_to_stack_compile_FST` (`pan_to_targetProofScript.sml:79-87`); `word_to_stack_compile`
    is the script's overload of the tagged `word_to_stack$compile` (`compileNative`), and HOL's free
    `mc wprog bitmaps c'' fs p` are explicit. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_to_stack_compile_FST"
  (words_as_type_indexed_bitvec)]
theorem word_to_stack_compile_FST {width : Nat} [NeZero width] {State Projection : Type}
    (mc : MachineConfig width State Projection)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (c'' : Compiler.Backend.WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × Compiler.Backend.StackLang.HolProg width)) :
    Compiler.Backend.WordToStack.Native.compileNative mc.target.config false wprog =
        (bitmaps, c'', fs, p) →
      p.map Prod.fst = raiseStubLocation :: storeConstsStubLocation :: wprog.map Prod.fst := by
  intro h
  simp only [Compiler.Backend.WordToStack.Native.compileNative, Bool.false_eq_true,
    ↓reduceIte] at h
  rcases hc : Compiler.Backend.WordToStack.Native.compileWordToStackNative mc.target.config false
    (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) wprog (.list [4], 1) with
    ⟨bodies, frames, bm⟩
  rw [hc] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, -, -, rfl⟩ := h
  simp only [List.map_cons]
  rw [WordToStackProofs.mapFstCompileWordToStack _ _ _ _ _ _ _ hc]

/-- HOL `good_dimindex_0w_8w` (`pan_to_targetProofScript.sml:249-256`): HOL's signed word `≤`
    is `BitVec.sle`; `good_dimindex (:α)` is the tagged `goodDimindex width`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "good_dimindex_0w_8w"
  (words_as_type_indexed_bitvec)]
theorem good_dimindex_0w_8w {width : Nat} [NeZero width] :
    goodDimindex width →
      (0 : BitVec width).sle 8 = true ∧ (-8 : BitVec width).sle 0 = true := by
  rintro (rfl | rfl) <;> decide

/-- stack_remove's total initializer keeps the endianness flag (Flapjack infrastructure for
    `full_make_init_be`; HOL unfolds `make_init_any_def`/`make_init_opt_def` and uses
    `stackProps$evaluate_consts`). -/
theorem makeInitAny_be {width : Nat} [NeZero width] {C F : Type}
    (ggc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × Compiler.Backend.StackLang.HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (Compiler.Backend.StackLang.HolProg width)) (s : StackSemStateFiniteExact width C F) :
    (Compiler.Backend.StackRemove.Proofs.InitMake.makeInitAny ggc maxHeap bitmaps dataSpace oracle
      jump bounds pointer code s).be = s.be := by
  unfold Compiler.Backend.StackRemove.Proofs.InitMake.makeInitAny
  cases h : Compiler.Backend.StackRemove.Proofs.InitMake.makeInitOpt ggc maxHeap bitmaps dataSpace
    oracle jump bounds pointer code s with
  | none => rfl
  | some t =>
    simp only
    unfold Compiler.Backend.StackRemove.Proofs.InitMake.makeInitOpt at h
    rcases run : StackSemEvaluate.evaluate
      (Compiler.Backend.StackRemove.initCode ggc maxHeap pointer, s) with ⟨r, post⟩
    rw [run] at h
    rcases r with _ | r
    · simp only at h
      split at h
      · simp only [Option.some.injEq] at h
        rw [← h]
        have := (Compiler.Backend.StackProps.evaluateConsts _ _ _ _ run).2.2.2.1
        simp [Compiler.Backend.StackRemove.Proofs.InitReduce.initReduce, this]
      · cases h
    · cases h

/-- HOL `full_make_init_be` (`pan_to_targetProofScript.sml:277-288`): the initial StackSem state
    keeps the LabSem endianness flag. HOL's free `a … k` are explicit, as in the tagged
    `full_make_init_ffi`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "full_make_init_be"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem full_make_init_be {width : Nat} [NeZero width] {C F : Type}
    (a : Compiler.Backend.StackToLab.Config) (b : Compiler.Backend.DataToWord.Config) (c d : Nat)
    (e : BitVec width × BitVec width) (f : List (BitVec width))
    (g : List (Nat × Compiler.Backend.StackLang.HolProg width))
    (h : Flapjack.Compiler.Backend.LabSem.State width C F) (i : Nat → Bool) (j : Nat)
    (k : Nat → C × List (Nat × Compiler.Backend.StackLang.HolProg width) × List (BitVec width)) :
    ((Compiler.Backend.StackToLab.Proofs.FullMakeInit.fullMakeInit a b c d e f g h i j k).1 :
      StackSemStateFiniteExact width C F).be = h.be := by
  simp only [Compiler.Backend.StackToLab.Proofs.FullMakeInit.fullMakeInit, Compiler.Backend.StackAlloc.makeInit,
    makeInitAny_be, Compiler.Backend.StackNames.makeInit, Compiler.Backend.StackToLab.Proofs.MakeInit.makeInit]

private def holFiniteMaptoBroadlookup {κ β : Type} (m : HolFiniteMapExact κ β) : κ → Option β :=
  m.lookup

private def holFiniteMapofBroad {κ β : Type} (lookup : κ → Option β)
    (finiteSupport : ∃ keys : List κ, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact κ β := ⟨lookup, finiteSupport⟩

/-- Canonical standalone-map witness for the `m` parameter of `FLOOKUP_MAP_KEYS_LINV`: the
    finite-support map roundtrips through its lookup and support proof. -/
theorem holFmapAsFiniteSupportParamWitness_FLOOKUP_MAP_KEYS_LINV_m {κ β : Type}
    (m : HolFiniteMapExact κ β) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup m) m.finiteSupport = m := by
  cases m
  rfl

/-- HOL `FLOOKUP_MAP_KEYS_LINV` (`pan_to_targetProofScript.sml:258-275`). HOL's free `f m i` are
    explicit; `f PERMUTES 𝕌(:α)` (`BIJ f UNIV UNIV`) is `Function.Bijective f`, `LINV` the tagged
    `holLinv` on `UNIV` (whose `[Nonempty α]` is HOL's type inhabitedness), `MAP_KEYS` the
    finite-support rendering `mapKeys`, and `FLOOKUP` is `lookup`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "FLOOKUP_MAP_KEYS_LINV"
  (fmap_as_finite_support_parameters := [m])]
theorem FLOOKUP_MAP_KEYS_LINV {α β : Type} [Nonempty α] (f : α → α) (m : HolFiniteMapExact α β)
    (i : α) :
    Function.Bijective f →
      (HolFiniteMapExact.mapKeys (holLinv f (fun _ => True)) m).lookup i = m.lookup (f i) := by
  intro hf
  have hinv : ∀ y, f (holLinv f (fun _ => True) y) = y := apply_holLinv_of_surjective hf.2
  have hlinj : Function.Injective (holLinv f (fun _ => True)) := fun x y h => by
    rw [← hinv x, ← hinv y, h]
  have hli : holLinv f (fun _ => True) (f i) = i := holLinv_apply_of_injective hf.1 i
  conv_lhs => rw [← hli]
  exact HolFiniteMapExact.lookup_mapKeys_of_injective hlinj m (f i)

/-- HOL `n2w_sub_alt` (`pan_to_targetProofScript.sml:1193-1201`, `[local]`). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "n2w_sub_alt"
  (words_as_type_indexed_bitvec)]
theorem n2w_sub_alt {width : Nat} [NeZero width] :
    ∀ a b : Nat, b ≤ a →
      (BitVec.ofNat width (a - b) : BitVec width) =
        BitVec.ofNat width a + -1 * BitVec.ofNat width b := by
  intro a b h
  have ha : BitVec.ofNat width a = BitVec.ofNat width (a - b) + BitVec.ofNat width b := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h]
  rw [ha]
  simp [BitVec.add_assoc, BitVec.add_right_neg]

/-- HOL `aligned_n2w_IMP` (`pan_to_targetProofScript.sml:1203-1209`, `[local]`); HOL's free
    `k n` are explicit, `aligned` is the tagged `holAligned`, `dimword (:α)` is `2 ^ width` and
    `divides` is `∣`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "aligned_n2w_IMP"
  (words_as_type_indexed_bitvec)]
theorem aligned_n2w_IMP {width : Nat} [NeZero width] (k n : Nat) :
    holAligned k (BitVec.ofNat width n : BitVec width) = true ∧ n < 2 ^ width → 2 ^ k ∣ n := by
  rintro ⟨ha, hn⟩
  simp only [holAligned, decide_eq_true_eq, holAlign_eq_div] at ha
  have h := congrArg BitVec.toNat ha
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h
  have hle : n / 2 ^ k * 2 ^ k ≤ n := Nat.div_mul_le_self n (2 ^ k)
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hn)] at h
  exact ⟨n / 2 ^ k, by rw [Nat.mul_comm]; exact h.symm⟩

/-- The first address of a short range does not recur later in it (Flapjack
    infrastructure for `word_list_exists_addresses`). -/
theorem not_mem_addresses_succ {width : Nat} [NeZero width] (good : goodDimindex width)
    (a : BitVec width) (m : Nat) (hb : (m + 1) * (width / 8) < 2 ^ width) :
    ¬ Compiler.Backend.StackRemove.addresses (a + Compiler.Backend.StackRemove.bytesInWord width) m a := by
  rw [Compiler.Backend.StackRemove.mem_addresses]
  rintro ⟨i, hi, eq⟩
  have pos : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  have zero : BitVec.ofNat width ((i + 1) * (width / 8)) = 0 := by
    have h := congrArg (fun z => z - a) eq
    simp only [BitVec.sub_self] at h
    rw [BitVec.add_assoc, BitVec.add_comm a, BitVec.add_sub_cancel] at h
    refine Eq.trans ?_ h.symm
    rw [Compiler.Backend.StackRemove.bytesInWord, ← BitVec.ofNat_mul_ofNat, BitVec.ofNat_add,
      BitVec.add_mul, BitVec.add_comm]
    simp
  have lt : (i + 1) * (width / 8) < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hb
  have := congrArg BitVec.toNat zero
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt] at this
  simp at this
  have : 0 < (i + 1) * (width / 8) := Nat.mul_pos (by omega) pos
  omega

/-- A forward word list exactly covering a short address range has the range's length
    (Flapjack infrastructure; HOL's induction on the list in `word_list_exists_addresses`). -/
theorem wordList_addresses_length {width : Nat} [NeZero width] {β : Type}
    (good : goodDimindex width) (d : BitVec width → β) :
    ∀ (xs : List β) (a : BitVec width) (m : Nat), m * (width / 8) < 2 ^ width →
      Misc.wordList a xs (SetSep.fun2Set (d, Compiler.Backend.StackRemove.addresses a m)) →
      xs.length = m := by
  intro xs
  induction xs with
  | nil =>
    intro a m _ h
    cases m with
    | zero => rfl
    | succ m =>
      have := congrFun h (a, d a)
      simp only [SetSep.fun2Set, eq_iff_iff, iff_false, not_exists, not_and] at this
      exact absurd (this a (Or.inl rfl)) (by simp)
  | cons x xs ih =>
    intro a m hb h
    obtain ⟨s1, s2, ⟨hunion, hdisj⟩, hs1, hw2⟩ := h
    simp only [SetSep.one] at hs1
    subst hs1
    have memS : ∀ e, SetSep.fun2Set (d, Compiler.Backend.StackRemove.addresses a m) e ↔
        (e = (a, x) ∨ s2 e) := fun e => by rw [← hunion]
    cases m with
    | zero =>
      have := (memS (a, x)).mpr (Or.inl rfl)
      obtain ⟨_, hmem, _⟩ := this
      exact absurd hmem (by simp [Compiler.Backend.StackRemove.addresses])
    | succ m =>
      have hx : x = d a := by
        obtain ⟨addr, hmem, he⟩ := (memS (a, x)).mpr (Or.inl rfl)
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rfl
      subst hx
      have hnot := not_mem_addresses_succ good a m hb
      have hs2 : s2 = SetSep.fun2Set (d, Compiler.Backend.StackRemove.addresses
          (a + Compiler.Backend.StackRemove.bytesInWord width) m) := by
        funext e
        apply propext
        constructor
        · intro he
          have hS := (memS e).mpr (Or.inr he)
          obtain ⟨addr, hmem, rfl⟩ := hS
          rcases hmem with rfl | hmem
          · exact absurd ⟨rfl, he⟩ (hdisj (addr, d addr))
          · exact ⟨addr, hmem, rfl⟩
        · rintro ⟨addr, hmem, rfl⟩
          have hS : SetSep.fun2Set (d, Compiler.Backend.StackRemove.addresses a (m + 1))
              (addr, d addr) := ⟨addr, Or.inr hmem, rfl⟩
          rcases (memS _).mp hS with heq | h2
          · simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, -⟩ := heq
            exact absurd hmem hnot
          · exact h2
      rw [hs2] at hw2
      have hb' : m * (width / 8) < 2 ^ width :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hb
      simp only [List.length_cons]
      rw [ih _ m hb' hw2]

/-- HOL `word_list_exists_addresses` (`pan_to_targetProofScript.sml:1211-1240`), the pan_to_target
    uniqueness form (distinct from stack_removeProof's existence theorem of the same name): a word
    list exactly covering a short address range has the range's length. HOL's free `a n d m` are
    explicit; `dimword (:α)` is `2 ^ width`, `w2n bytes_in_word` is `(bytesInWord width).toNat` and
    `good_dimindex` the tagged `goodDimindex`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_list_exists_addresses"
  (words_as_type_indexed_bitvec)]
theorem word_list_exists_addresses {width : Nat} [NeZero width] {β : Type} (a : BitVec width)
    (n : Nat) (d : BitVec width → β) (m : Nat) :
    Misc.wordListExists a n (SetSep.fun2Set (d, Compiler.Backend.StackRemove.addresses a m)) ∧
      goodDimindex width ∧ m < 2 ^ width / (Compiler.Backend.StackRemove.bytesInWord width).toNat →
    n = m := by
  rintro ⟨⟨xs, s1, s2, ⟨hunion, -⟩, hw, hc, hlen⟩, good, hm⟩
  have hb : (Compiler.Backend.StackRemove.bytesInWord width).toNat = width / 8 := by
    rcases good with rfl | rfl <;> rfl
  have pos : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  rw [hb] at hm
  have bound : m * (width / 8) < 2 ^ width := by
    have := Nat.mul_le_of_le_div (width / 8) (m + 1) (2 ^ width) hm
    rw [Nat.succ_mul] at this
    omega
  have hs : s1 = SetSep.fun2Set (d, Compiler.Backend.StackRemove.addresses a m) := by
    rw [← hunion, hc]
    funext e
    simp
  rw [hs] at hw
  rw [← hlen]
  exact wordList_addresses_length good d xs a m bound hw

/-- HOL `good_dimindex_div_mul` (`pan_to_targetProofScript.sml:1242-1248`); HOL's free `a` is
    explicit and `dimindex (:α)` is the word width. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "good_dimindex_div_mul"
  (word_dimension_as_width := width)]
theorem good_dimindex_div_mul (width : Nat) [NeZero width] (a : Nat) :
    goodDimindex width → a * width / 8 = a * (width / 8) := by
  rintro (rfl | rfl) <;> omega

/-- HOL `InitGlobals_location_eq_first_name` (`pan_to_targetProofScript.sml:1250-1254`). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "InitGlobals_location_eq_first_name"]
theorem InitGlobals_location_eq_first_name :
    Compiler.Backend.BvlToBvi.initGlobalsLocation = firstLoopName := by
  decide

end Flapjack.Pancake.Proofs.PanToTarget
