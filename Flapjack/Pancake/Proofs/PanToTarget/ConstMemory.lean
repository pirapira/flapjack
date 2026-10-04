import Flapjack.Misc.SetSep
import Flapjack.Compiler.Backend.Semantics.WordSem.Inst
import Flapjack.Compiler.Backend.Semantics.WordSem.ShMem
import Flapjack.Compiler.Backend.Semantics.WordSem.Env
import Flapjack.Misc.Option
import Flapjack.HolArb
import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers

/-! pan_to_targetProofScript.sml 336-606: WordSem operations only observe
memory through its graph `fun2set (memory, mdomain)`. HOL's memory domain is a
set; the WordSem carrier renders it as a `Bool` predicate and set_sep's
`fun2set` takes a `Prop` predicate, so a domain `md` appears in graphs as
`fun a => md a = true`, the identity reading of the same HOL set. -/
namespace Flapjack.Pancake.Proofs.PanToTarget.ConstMemory
open Flapjack Flapjack.SetSep

/-- Canonical WordSem codec for the owning source carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Graph equality is pointwise agreement on the domain (Flapjack
infrastructure; HOL uses `set_sep$fun2set_eq`). -/
theorem fun2Set_eq_iff {α β : Type} (m m' : α → β) (md : α → Prop) :
    fun2Set (m, md) = fun2Set (m', md) ↔ ∀ a, md a → m a = m' a := by
  constructor
  · intro h a ha
    have member : fun2Set (m, md) (a, m a) := ⟨a, ha, rfl⟩
    rw [h] at member
    obtain ⟨b, _, eq⟩ := member
    obtain ⟨rfl, value⟩ := Prod.mk.inj eq
    exact value
  · intro h
    funext ⟨a, v⟩
    apply propext
    constructor
    · rintro ⟨b, hb, eq⟩
      exact ⟨b, hb, by simpa [h b hb] using eq⟩
    · rintro ⟨b, hb, eq⟩
      exact ⟨b, hb, by simpa [h b hb] using eq⟩

/-- Full original fun2set_update_eq (337-344) for arbitrary address/value
types: updating two memories with the same graph at the same address keeps
their graphs equal. HOL's `m⦇x ↦ a⦈` is the pointwise `if` update used by
the WordSem carrier. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "fun2set_update_eq"]
theorem fun2SetUpdateEq {α β : Type} [DecidableEq α] (m m' : α → β) (md : α → Prop)
    (x : α) (a : β) (h : fun2Set (m, md) = fun2Set (m', md)) :
    fun2Set ((fun y => if y = x then a else m y), md) =
      fun2Set ((fun y => if y = x then a else m' y), md) := by
  rw [fun2Set_eq_iff] at h ⊢
  intro b hb
  by_cases hbx : b = x
  · simp [hbx]
  · simp [hbx, h b hb]

section Accessors

/-- Full original get_var_const_memory (346-350). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "get_var_const_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarConstMemory {width : Nat} [NeZero width] {C F : Type} (x : Nat) (y : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) :
    WordSemStateFiniteExact.getVar x { y with memory := m } = WordSemStateFiniteExact.getVar x y := rfl

/-- Full original set_var_const_memory (352-356). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "set_var_const_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVarConstMemory {width : Nat} [NeZero width] {C F : Type} (v : Nat) (x : WordLocW width) (y : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width) :
    WordSemStateFiniteExact.setVar v x { y with memory := m } = { WordSemStateFiniteExact.setVar v x y with memory := m } := rfl

/-- Full original unset_var_const_memory (358-362). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "unset_var_const_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem unsetVarConstMemory {width : Nat} [NeZero width] {C F : Type} (v : Nat) (y : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) :
    WordSemStateFiniteExact.unsetVar v { y with memory := m } = { WordSemStateFiniteExact.unsetVar v y with memory := m } := rfl

/-- Full original get_vars_const_memory (364-368), by induction on the list. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "get_vars_const_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarsConstMemory {width : Nat} [NeZero width] {C F : Type} (x : List Nat) (y : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) :
    WordSemStateFiniteExact.getVars x { y with memory := m } = WordSemStateFiniteExact.getVars x y := by
  induction x with
  | nil => rfl
  | cons v vs ih => simp only [WordSemStateFiniteExact.getVars, ih]; rfl

/-- Full original set_vars_const_memory (370-374). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "set_vars_const_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVarsConstMemory {width : Nat} [NeZero width] {C F : Type} (vs : List Nat) (xs : List (WordLocW width)) (y : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width) :
    WordSemStateFiniteExact.setVars vs xs { y with memory := m } = { WordSemStateFiniteExact.setVars vs xs y with memory := m } := rfl

/-- Full original get_var_imm_const_memory (376-380). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "get_var_imm_const_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarImmConstMemory {width : Nat} [NeZero width] {C F : Type} (ri : WordRegImm (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width) :
    WordSemStateFiniteExact.getVarImm ri { s with memory := m } = WordSemStateFiniteExact.getVarImm ri s := by
  cases ri <;> rfl

/-- Full original mem_load_const_memory (382-388). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_load_const_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem memLoadConstMemory {width : Nat} [NeZero width] {C F : Type} (ad : BitVec width) (s : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width)
    (h : fun2Set (s.memory, fun a => s.mdomain a = true) =
      fun2Set (m, fun a => s.mdomain a = true)) :
    WordSemStateFiniteExact.memLoad ad { s with memory := m } = WordSemStateFiniteExact.memLoad ad s := by
  rw [fun2Set_eq_iff] at h
  unfold WordSemStateFiniteExact.memLoad
  by_cases hd : s.mdomain ad = true
  · simp [hd, h ad hd]
  · simp [hd]

/-- Full original mem_store_const_memory (390-398): both the failure and the
exact success shape transfer between graph-equal memories. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_store_const_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem memStoreConstMemory {width : Nat} [NeZero width] {C F : Type} (ad : BitVec width) (w : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width)
    (_h : fun2Set (s.memory, fun a => s.mdomain a = true) =
      fun2Set (m, fun a => s.mdomain a = true)) :
    (WordSemStateFiniteExact.memStore ad w s = none ↔ WordSemStateFiniteExact.memStore ad w { s with memory := m } = none) ∧
    (WordSemStateFiniteExact.memStore ad w s =
        some { s with memory := fun a => if a = ad then w else s.memory a } ↔
      WordSemStateFiniteExact.memStore ad w { s with memory := m } =
        some { s with memory := fun a => if a = ad then w else m a }) := by
  unfold WordSemStateFiniteExact.memStore
  by_cases hd : s.mdomain ad = true <;> simp [hd]

end Accessors

section Bytes

/-- Memories are inhabited (needed for HOL's THE on an optional memory). -/
instance memoryNonempty {width : Nat} [NeZero width] : Nonempty (BitVec width → WordLocW width) := ⟨fun _ => .word 0⟩

/-- Full original mem_load_32_const_memory (400-407). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_load_32_const_memory"
  (words_as_type_indexed_bitvec)]
theorem memLoad32ConstMemory {width : Nat} [NeZero width] (m m' : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (be : Bool) (ad : BitVec width)
    (h : fun2Set (m, fun a => dm a = true) = fun2Set (m', fun a => dm a = true)) :
    memLoad32Exact m dm be ad = memLoad32Exact m' dm be ad := by
  rw [fun2Set_eq_iff] at h
  unfold memLoad32Exact
  by_cases hd : dm (riscvByteAlignHOL ad) = true
  · rw [h _ hd]
  · rw [Bool.not_eq_true] at hd
    by_cases ha : riscvAlignedHOL 2 ad = true <;> simp only [ha, hd, if_true, if_false,
      Bool.false_eq_true] <;>
      (cases m (riscvByteAlignHOL ad) <;> cases m' (riscvByteAlignHOL ad) <;> rfl)

/-- Full original mem_store_32_const_memory (409-419): failure transfers and
the stored memories keep equal graphs (HOL's THE is holThe). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_store_32_const_memory"
  (words_as_type_indexed_bitvec)]
theorem memStore32ConstMemory {width : Nat} [NeZero width] (m m' : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (be : Bool) (ad : BitVec width) (hw : BitVec 32)
    (h : fun2Set (m, fun a => dm a = true) = fun2Set (m', fun a => dm a = true)) :
    (memStore32Exact m dm be ad hw = none ↔ memStore32Exact m' dm be ad hw = none) ∧
    fun2Set (holThe (memStore32Exact m dm be ad hw), fun a => dm a = true) =
      fun2Set (holThe (memStore32Exact m' dm be ad hw), fun a => dm a = true) := by
  rw [fun2Set_eq_iff] at h
  by_cases hd : dm (riscvByteAlignHOL ad) = true
  · unfold memStore32Exact
    rw [h _ hd]
    by_cases ha : riscvAlignedHOL 2 ad = true
    · simp only [ha, if_true, hd]
      cases m' (riscvByteAlignHOL ad) with
      | word v =>
        refine ⟨by simp, ?_⟩
        rw [fun2Set_eq_iff]
        intro a ha'
        simp only [holThe]
        split
        · rfl
        · exact h a ha'
      | loc _ _ => exact ⟨Iff.rfl, rfl⟩
    · simp only [ha, Bool.false_eq_true, if_false]
      exact ⟨trivial, trivial⟩
  · rw [Bool.not_eq_true] at hd
    have none32 : memStore32Exact m dm be ad hw = none ∧ memStore32Exact m' dm be ad hw = none := by
      unfold memStore32Exact
      by_cases ha : riscvAlignedHOL 2 ad = true <;> simp only [ha, hd, if_true, if_false,
        Bool.false_eq_true] <;>
        (constructor <;> (first | (cases m (riscvByteAlignHOL ad) <;> simp) |
          (cases m' (riscvByteAlignHOL ad) <;> simp) | rfl))
    rw [show memStore32Exact m dm be ad hw = _ from none32.1,
      show memStore32Exact m' dm be ad hw = _ from none32.2]
    exact ⟨Iff.rfl, rfl⟩

end Bytes

section Expressions

/-- Full original word_exp_const_memory (421-434), by recursion on the
expression as HOL's word_exp_ind. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_exp_const_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExpConstMemory {width : Nat} [NeZero width] {C F : Type} (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width)
    (h : fun2Set (s.memory, fun a => s.mdomain a = true) =
      fun2Set (m, fun a => s.mdomain a = true)) :
    ∀ exp : WordLangExpHOL (BitVec width),
      WordSemStateFiniteExact.wordExp { s with memory := m } exp = WordSemStateFiniteExact.wordExp s exp
  | .const _ => by simp only [WordSemStateFiniteExact.wordExp]
  | .var _ => by simp only [WordSemStateFiniteExact.wordExp]; rfl
  | .lookup _ => by simp only [WordSemStateFiniteExact.wordExp]; rfl
  | .load address => by
      simp only [WordSemStateFiniteExact.wordExp, wordExpConstMemory s m h address]
      split
      · exact memLoadConstMemory _ s m h
      · rfl
  | .op operator args => by
      simp only [WordSemStateFiniteExact.wordExp]
      have same : (args.attach.map fun ⟨e, _⟩ => WordSemStateFiniteExact.wordExp { s with memory := m } e) =
          (args.attach.map fun ⟨e, _⟩ => WordSemStateFiniteExact.wordExp s e) := by
        apply List.map_congr_left
        rintro ⟨e, he⟩ _
        exact wordExpConstMemory s m h e
      rw [same]
  | .shift _ left right => by
      simp only [WordSemStateFiniteExact.wordExp, wordExpConstMemory s m h left, wordExpConstMemory s m h right]
termination_by exp => sizeOf exp
decreasing_by
  all_goals simp_wf
  all_goals (try have := List.sizeOf_lt_of_mem he)
  all_goals omega

end Expressions

section ByteArrays

/-- Full original mem_load_byte_aux_const_memory (436-445). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_load_byte_aux_const_memory"
  (words_as_type_indexed_bitvec)]
theorem memLoadByteAuxConstMemory {width : Nat} [NeZero width] (m m' : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (be : Bool) (w : BitVec width)
    (h : fun2Set (m, fun a => dm a = true) = fun2Set (m', fun a => dm a = true)) :
    memLoadByteAuxExact m' dm be w = memLoadByteAuxExact m dm be w := by
  rw [fun2Set_eq_iff] at h
  unfold memLoadByteAuxExact
  by_cases hd : dm (riscvByteAlignHOL w) = true
  · rw [h _ hd]
  · rw [Bool.not_eq_true] at hd
    simp only [hd, Bool.false_eq_true, if_false]
    cases m (riscvByteAlignHOL w) <;> cases m' (riscvByteAlignHOL w) <;> rfl

/-- Full original mem_store_byte_aux_const_memory (447-461): failure
transfers and the stored memories keep equal graphs (HOL's THE is holThe). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_store_byte_aux_const_memory"
  (words_as_type_indexed_bitvec)]
theorem memStoreByteAuxConstMemory {width : Nat} [NeZero width] (m m' : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (be : Bool) (w : BitVec width) (b : BitVec 8)
    (h : fun2Set (m, fun a => dm a = true) = fun2Set (m', fun a => dm a = true)) :
    (memStoreByteAuxExact m dm be w b = none ↔ memStoreByteAuxExact m' dm be w b = none) ∧
    fun2Set (holThe (memStoreByteAuxExact m' dm be w b), fun a => dm a = true) =
      fun2Set (holThe (memStoreByteAuxExact m dm be w b), fun a => dm a = true) := by
  rw [fun2Set_eq_iff] at h
  by_cases hd : dm (riscvByteAlignHOL w) = true
  · unfold memStoreByteAuxExact
    rw [h _ hd]
    cases m' (riscvByteAlignHOL w) with
    | word v =>
      simp only [hd, if_true]
      refine ⟨by simp, ?_⟩
      rw [fun2Set_eq_iff]
      intro a ha
      simp only [holThe]
      split
      · rfl
      · exact (h a ha).symm
    | loc _ _ => exact ⟨Iff.rfl, rfl⟩
  · rw [Bool.not_eq_true] at hd
    have none1 : memStoreByteAuxExact m dm be w b = none := by
      unfold memStoreByteAuxExact; cases m (riscvByteAlignHOL w) <;> simp [hd]
    have none2 : memStoreByteAuxExact m' dm be w b = none := by
      unfold memStoreByteAuxExact; cases m' (riscvByteAlignHOL w) <;> simp [hd]
    rw [none1, none2]
    exact ⟨Iff.rfl, rfl⟩

/-- Full original read_bytearray_const_memory (463-471): graph-equal memories
read the same byte arrays through mem_load_byte_aux. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "read_bytearray_const_memory"
  (words_as_type_indexed_bitvec)]
theorem readBytearrayConstMemory {width : Nat} [NeZero width] (m m' : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (be : Bool) (ptr : BitVec width) (len : Nat)
    (h : fun2Set (m, fun a => dm a = true) = fun2Set (m', fun a => dm a = true)) :
    readBytearrayWordHOL ptr len (memLoadByteAuxExact m dm be) =
      readBytearrayWordHOL ptr len (memLoadByteAuxExact m' dm be) := by
  have same : memLoadByteAuxExact m dm be = memLoadByteAuxExact m' dm be := by
    funext w
    exact (memLoadByteAuxConstMemory m m' dm be w h).symm
  rw [same]

/-- Full original write_bytearray_const_memory (473-485), for all byte lists,
addresses and graph-equal memories. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "write_bytearray_const_memory"
  (words_as_type_indexed_bitvec)]
theorem writeBytearrayConstMemory {width : Nat} [NeZero width] (m' : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (be : Bool) :
    ∀ (ls : List (BitVec 8)) (ptr : BitVec width) (m : BitVec width → WordLocW width),
      fun2Set (m, fun a => dm a = true) = fun2Set (m', fun a => dm a = true) →
      fun2Set (writeBytearrayExact ptr ls m dm be, fun a => dm a = true) =
        fun2Set (writeBytearrayExact ptr ls m' dm be, fun a => dm a = true) := by
  intro ls
  induction ls with
  | nil => intro ptr m h; exact h
  | cons byte rest ih =>
    intro ptr m h
    have tail := ih (ptr + 1) m h
    have stored := memStoreByteAuxConstMemory _ _ dm be ptr byte tail
    simp only [writeBytearrayExact]
    rcases h1 : memStoreByteAuxExact (writeBytearrayExact (ptr + 1) rest m dm be) dm be ptr byte
      with _ | m1
    · rcases h2 : memStoreByteAuxExact (writeBytearrayExact (ptr + 1) rest m' dm be) dm be ptr byte
        with _ | m2
      · exact h
      · rw [h1, h2] at stored; simp at stored
    · rcases h2 : memStoreByteAuxExact (writeBytearrayExact (ptr + 1) rest m' dm be) dm be ptr byte
        with _ | m2
      · rw [h1, h2] at stored; simp at stored
      · rw [h1, h2] at stored
        exact stored.2.symm

/-- Full original const_writes_const_memory (532-541). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "const_writes_const_memory"
  (words_as_type_indexed_bitvec)]
theorem constWritesConstMemory {width : Nat} [NeZero width] :
    ∀ (c' c : BitVec width) (words : List (Bool × BitVec width))
      (m m' : BitVec width → WordLocW width) (md : BitVec width → Prop),
      fun2Set (m, md) = fun2Set (m', md) →
      fun2Set (wordSemConstWrites c' c words m, md) =
        fun2Set (wordSemConstWrites c' c words m', md) := by
  intro c' c words
  induction words generalizing c' with
  | nil => intro m m' md h; exact h
  | cons entry rest ih =>
    intro m m' md h
    rcases entry with ⟨b, x⟩
    simp only [wordSemConstWrites]
    apply ih
    rw [fun2Set_eq_iff] at h ⊢
    intro a ha
    by_cases hax : a = c' <;> simp [hax, h a ha]

end ByteArrays

section States

/-- Shared-memory commutation summary for one operation (Flapjack factoring
of the share_inst_const_memory case split; no HOL original). -/
private def Commutes {width : Nat} [NeZero width] {C F : Type} {rw : Nat} [NeZero rw]
    (r : Option (WordSemResult rw) × WordSemStateFiniteExact width C F) (s : WordSemStateFiniteExact width C F)
    (r' : Option (WordSemResult rw) × WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) :
    Prop :=
  r' = (r.1, { r.2 with memory := m }) ∧ r.2.memory = s.memory ∧ r.2.mdomain = s.mdomain

private theorem setVarCommutes {width : Nat} [NeZero width] {C F : Type} {rw : Nat} [NeZero rw] (x : Option (HolFfiResult F)) (v : Nat)
    (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) :
    Commutes (WordSemStateFiniteExact.shMemSetVar (rw := rw) x v s) s (WordSemStateFiniteExact.shMemSetVar x v { s with memory := m }) m := by
  rcases x with _ | ⟨_⟩ | ⟨_, _⟩ <;> exact ⟨rfl, rfl, rfl⟩

private theorem storeCommutes {width : Nat} [NeZero width] {C F : Type} {rw : Nat} [NeZero rw] (ffiResult : HolFfiResult F)
    (guard : Bool) (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) :
    Commutes (rw := rw)
      (if guard = true then
        match ffiResult with
        | .final outcome => (some (.finalFfi outcome), WordSemStateFiniteExact.flushState true s)
        | .ret newFfi _ => (none, { s with ffi := newFfi })
      else (some .error, s)) s
      (if guard = true then
        match ffiResult with
        | .final outcome => (some (.finalFfi outcome), WordSemStateFiniteExact.flushState true { s with memory := m })
        | .ret newFfi _ => (none, { { s with memory := m } with ffi := newFfi })
      else (some .error, { s with memory := m })) m := by
  cases guard <;> simp only [Bool.false_eq_true, if_false, if_true]
  · exact ⟨rfl, rfl, rfl⟩
  · cases ffiResult <;> exact ⟨rfl, rfl, rfl⟩

/-- Full original share_inst_const_memory (543-565): shared-memory
instructions leave memory and its domain unchanged and commute with replacing
the memory. The result width is the shareInst result carrier. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "share_inst_const_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem shareInstConstMemory {width : Nat} [NeZero width] {C F : Type} {rw : Nat} [NeZero rw] (res : Option (WordSemResult rw)) :
    ∀ (s : WordSemStateFiniteExact width C F) (op : WordMemOp) (v : Nat) (c : BitVec width)
      (m : BitVec width → WordLocW width) (t : WordSemStateFiniteExact width C F),
      fun2Set (s.memory, fun a => s.mdomain a = true) =
          fun2Set (m, fun a => s.mdomain a = true) ∧
        WordSemStateFiniteExact.shareInst op v c s = (res, t) →
      t.memory = s.memory ∧ t.mdomain = s.mdomain ∧
        WordSemStateFiniteExact.shareInst op v c { s with memory := m } = (res, { t with memory := m }) := by
  intro s op v c m t ⟨_, run⟩
  have commutes : Commutes (WordSemStateFiniteExact.shareInst (rw := rw) op v c s) s
      (WordSemStateFiniteExact.shareInst op v c { s with memory := m }) m := by
    cases op
    case load => exact setVarCommutes _ v s m
    case load8 => exact setVarCommutes _ v s m
    case load16 => exact setVarCommutes _ v s m
    case load32 => exact setVarCommutes _ v s m
    all_goals
      simp only [WordSemStateFiniteExact.shareInst, WordSemStateFiniteExact.getVar]
      split
      · simp only [WordSemStateFiniteExact.shMemStore, WordSemStateFiniteExact.shMemStoreByte, WordSemStateFiniteExact.shMemStore16, WordSemStateFiniteExact.shMemStore32]
        exact storeCommutes _ _ s m
      · exact ⟨rfl, rfl, rfl⟩
  rw [run] at commutes
  exact ⟨commutes.2.1, commutes.2.2, commutes.1⟩

/-- Original local push_env_mem_upd (574-584): push_env commutes with
replacing the memory. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "push_env_mem_upd"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnvMemUpd {width : Nat} [NeZero width] {C F : Type} (m : BitVec width → WordLocW width) :
    ∀ (env : Spt (WordLocW width) × Spt (WordLocW width))
      (params : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
      (s : WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.pushEnv env params { s with memory := m } =
        { WordSemStateFiniteExact.pushEnv env params s with memory := m } := by
  intro env params s
  cases params with
  | none => rfl
  | some p => rcases p with ⟨_, _, _, _⟩; rfl

/-- Original local push_env_mem_const (586-596): push_env keeps memory and
domain. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "push_env_mem_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnvMemConst {width : Nat} [NeZero width] {C F : Type} :
    ∀ (env : Spt (WordLocW width) × Spt (WordLocW width))
      (params : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
      (s : WordSemStateFiniteExact width C F),
      (WordSemStateFiniteExact.pushEnv env params s).memory = s.memory ∧
        (WordSemStateFiniteExact.pushEnv env params s).mdomain = s.mdomain := by
  intro env params s
  cases params with
  | none => exact ⟨rfl, rfl⟩
  | some p => rcases p with ⟨_, _, _, _⟩; exact ⟨rfl, rfl⟩

/-- Original local cut_state_with_mem_const (598-605). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "cut_state_with_mem_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cutStateWithMemConst {width : Nat} [NeZero width] {C F : Type} (x : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width) :
    WordSemStateFiniteExact.cutState x { s with memory := m } =
      (WordSemStateFiniteExact.cutState x s).map (fun s' => { s' with memory := m }) := by
  unfold WordSemStateFiniteExact.cutState
  cases wordSemCutEnv x s.locals <;> simp

/-- Original local mem_upd_lemma (567-572): states equal after overwriting
memory by HOL's ARB (rendered holArb) differ only in memory. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_upd_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem memUpdLemma {width : Nat} [NeZero width] {C F : Type} (s t : WordSemStateFiniteExact width C F)
    (h : { s with memory := @holArb (BitVec width → WordLocW width) ⟨fun _ => .word 0⟩ } =
      { t with memory := @holArb (BitVec width → WordLocW width) ⟨fun _ => .word 0⟩ }) :
    ∃ m, s = { t with memory := m } := by
  refine ⟨s.memory, ?_⟩
  cases s; cases t
  simp only [WordSemStateFiniteExact.mk.injEq] at h ⊢
  simp_all

end States

section Instructions

/-- Instruction results agree up to a graph-equal memory (Flapjack factoring
of inst_const_memory; no HOL original). -/
private def Agree {width : Nat} [NeZero width] {C F : Type} (o o' : Option (WordSemStateFiniteExact width C F)) : Prop :=
  (o = none ∧ o' = none) ∨
    ∃ x m', o = some x ∧ o' = some { x with memory := m' } ∧
      fun2Set (x.memory, fun a => x.mdomain a = true) =
        fun2Set (m', fun a => x.mdomain a = true)

private theorem agreeMap {width : Nat} [NeZero width] {C F : Type} (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width)
    (h : fun2Set (s.memory, fun a => s.mdomain a = true) =
      fun2Set (m, fun a => s.mdomain a = true))
    (o : Option (WordSemStateFiniteExact width C F))
    (frame : ∀ x, o = some x → x.memory = s.memory ∧ x.mdomain = s.mdomain) :
    Agree o (o.map fun x => { x with memory := m }) := by
  rcases o with _ | x
  · exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨hm, hd⟩ := frame x rfl
    exact Or.inr ⟨x, m, rfl, rfl, by rw [hm, hd]; exact h⟩

private theorem getFpVarMem {width : Nat} [NeZero width] {C F : Type} (x : Nat) (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) :
    WordSemStateFiniteExact.getFpVar x { s with memory := m } = WordSemStateFiniteExact.getFpVar x s := rfl

/-- Memory-free instructions commute with replacing memory and keep memory
and domain (Flapjack factoring of inst_const_memory). -/
private theorem mapCase {width : Nat} [NeZero width] {C F : Type} (i : WordLangInst (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width)
    (h : fun2Set (s.memory, fun a => s.mdomain a = true) =
      fun2Set (m, fun a => s.mdomain a = true))
    (eq : WordSemStateFiniteExact.inst i { s with memory := m } = (WordSemStateFiniteExact.inst i s).map fun x => { x with memory := m })
    (frame : ∀ x, WordSemStateFiniteExact.inst i s = some x → x.memory = s.memory ∧ x.mdomain = s.mdomain) :
    Agree (WordSemStateFiniteExact.inst i s) (WordSemStateFiniteExact.inst i { s with memory := m }) := by
  rw [eq]
  exact agreeMap s m h _ frame

private theorem instAgree {width : Nat} [NeZero width] {C F : Type} (i : WordLangInst (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width)
    (h : fun2Set (s.memory, fun a => s.mdomain a = true) =
      fun2Set (m, fun a => s.mdomain a = true)) :
    Agree (WordSemStateFiniteExact.inst i s) (WordSemStateFiniteExact.inst i { s with memory := m }) := by
  have expEq := wordExpConstMemory s m h
  have graph := h
  rw [fun2Set_eq_iff] at graph
  rcases i with _ | ⟨r, w⟩ | a | ⟨op, r, ⟨ad, off⟩⟩ | f
  case mem =>
    have loadEq := fun ad => memLoadConstMemory ad s m h
    have byteEq := fun w => memLoadByteAuxConstMemory s.memory m s.mdomain s.be w h
    have word32Eq := fun w => memLoad32ConstMemory s.memory m s.mdomain s.be w h
    cases op
    case load16 => exact Or.inl ⟨rfl, rfl⟩
    case store16 => exact Or.inl ⟨rfl, rfl⟩
    case load | load8 | load32 =>
      apply mapCase _ s m h
      · simp only [WordSemStateFiniteExact.inst, expEq, loadEq, byteEq, ← word32Eq]
        split <;> (try split) <;> rfl
      · intro x hx
        simp only [WordSemStateFiniteExact.inst] at hx
        repeat' (split at hx)
        all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hx)
        all_goals (try subst hx)
        all_goals (try exact ⟨rfl, rfl⟩)
    case store =>
      simp only [WordSemStateFiniteExact.inst, expEq, getVarConstMemory]
      split
      · rename_i a w _ _
        unfold WordSemStateFiniteExact.memStore
        by_cases hd : s.mdomain a = true
        · simp only [hd, if_true]
          exact Or.inr ⟨_, _, rfl, rfl, fun2SetUpdateEq s.memory m _ a w h⟩
        · simp only [hd, Bool.false_eq_true, if_false]
          exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
    case store8 =>
      simp only [WordSemStateFiniteExact.inst, expEq, getVarConstMemory]
      split
      · rename_i a w _ _
        have stored := memStoreByteAuxConstMemory s.memory m s.mdomain s.be a (w.setWidth 8) h
        rcases h1 : memStoreByteAuxExact s.memory s.mdomain s.be a (w.setWidth 8) with _ | n1 <;>
          rcases h2 : memStoreByteAuxExact m s.mdomain s.be a (w.setWidth 8) with _ | n2 <;>
          rw [h1, h2] at stored
        · exact Or.inl ⟨rfl, rfl⟩
        · exact absurd (stored.1.mp rfl) (by simp)
        · exact absurd (stored.1.mpr rfl) (by simp)
        · exact Or.inr ⟨_, n2, rfl, rfl, by simpa only [holThe] using stored.2.symm⟩
      · exact Or.inl ⟨rfl, rfl⟩
    case store32 =>
      simp only [WordSemStateFiniteExact.inst, expEq, getVarConstMemory]
      split
      · rename_i a w _ _
        have stored := memStore32ConstMemory s.memory m s.mdomain s.be a (w.setWidth 32) h
        rcases h1 : memStore32Exact s.memory s.mdomain s.be a (w.setWidth 32) with _ | n1 <;>
          rcases h2 : memStore32Exact m s.mdomain s.be a (w.setWidth 32) with _ | n2 <;>
          rw [h1, h2] at stored
        · exact Or.inl ⟨rfl, rfl⟩
        · exact absurd (stored.1.mp rfl) (by simp)
        · exact absurd (stored.1.mpr rfl) (by simp)
        · exact Or.inr ⟨_, n2, rfl, rfl, by simpa only [holThe] using stored.2⟩
      · exact Or.inl ⟨rfl, rfl⟩
  case arith =>
    rcases a with ⟨_, _, _, ri⟩ | ⟨_, _, _, ri⟩ | _ | _ | _ | _ | _ | _
    all_goals (try cases ri)
    all_goals
      apply mapCase _ s m h
      · simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.assign, expEq, getVarsConstMemory]
        split <;> (try split) <;> rfl
      · intro x hx
        simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.assign] at hx
        repeat' (split at hx)
        all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hx)
        all_goals (try subst hx)
        all_goals (try exact ⟨rfl, rfl⟩)
  case fp =>
    cases f
    all_goals
      apply mapCase _ s m h
      · simp only [WordSemStateFiniteExact.inst, getFpVarMem, getVarConstMemory]
        repeat' (first | rfl | split)
      · intro x hx
        simp only [WordSemStateFiniteExact.inst] at hx
        repeat' (split at hx)
        all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hx)
        all_goals (try subst hx)
        all_goals (try exact ⟨rfl, rfl⟩)
  all_goals
    apply mapCase _ s m h
    · simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.assign, expEq]
      first | rfl | (split <;> rfl)
    · intro x hx
      simp only [WordSemStateFiniteExact.inst, WordSemStateFiniteExact.assign] at hx
      repeat' (split at hx)
      all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hx)
      all_goals (try subst hx)
      all_goals (try exact ⟨rfl, rfl⟩)

/-- Full original inst_const_memory (487-530): for graph-equal memories an
instruction fails on both or on neither, and on success the results differ
only by a graph-equal memory. HOL's THE is holThe (Nonempty from the state
itself; the arbitrary THE NONE value is unused). The inst rendering's
reals_as_rational_cuts assumption is inherited (SOUNDNESS item 8). -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "inst_const_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem instConstMemory {width : Nat} [NeZero width] {C F : Type} (i : WordLangInst (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width)
    (h : fun2Set (s.memory, fun a => s.mdomain a = true) =
      fun2Set (m, fun a => s.mdomain a = true)) :
    (WordSemStateFiniteExact.inst i s = none ↔ WordSemStateFiniteExact.inst i { s with memory := m } = none) ∧
    (WordSemStateFiniteExact.inst i s ≠ none →
      ∃ m', @holThe _ ⟨s⟩ (WordSemStateFiniteExact.inst i { s with memory := m }) =
          { @holThe _ ⟨s⟩ (WordSemStateFiniteExact.inst i s) with memory := m' } ∧
        (let x := @holThe _ ⟨s⟩ (WordSemStateFiniteExact.inst i s)
         fun2Set (x.memory, fun a => x.mdomain a = true) =
           fun2Set (m', fun a => x.mdomain a = true))) := by
  rcases instAgree i s m h with ⟨h1, h2⟩ | ⟨x, m', h1, h2, g⟩
  · rw [h1, h2]
    exact ⟨Iff.rfl, fun hne => absurd rfl hne⟩
  · rw [h1, h2]
    exact ⟨by simp, fun _ => ⟨m', rfl, g⟩⟩

end Instructions

end Flapjack.Pancake.Proofs.PanToTarget.ConstMemory
