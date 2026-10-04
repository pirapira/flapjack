import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Frame

/-!
# `word_to_wordProof` `compile_single_correct`: leaf cases

The statement of HOL `compile_single_correct` (`word_to_wordProofScript.sml:235-256`)
at one program and state, and its leaf `Resume` cases (`Skip` … `ShareInst`),
which HOL closes by `evaluate_def` and `state_component_equality`: a leaf runs
the same on the compiled code table, so the identity permutation works.
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm

namespace CompileSingleCorrectLeafCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompileSingleCorrectLeafCarrier

open Classical in
/-- HOL `compile_single_correct` at one program and state, with HOL's free
    `tt kk aa co` as parameters (Flapjack infrastructure naming the induction
    motive). HOL's `(I ## MAP f) o oracle` is `Prod.map id (List.map f) ∘ oracle`. -/
def CompileSingleCorrectAt {width : Nat} [NeZero width] {C F : Type} (tt : Bool) (kk aa : Nat)
    (co : AsmConfigExact width) (prog : WordLangProgHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F) : Prop :=
  ∀ (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (coracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C)),
    codeRel st.code l ∧ sptDomain st.code = sptDomain l ∧
      st.compile = (fun conf progs => cc conf (progs.map (fun p => compileSingle tt kk aa co (p, none)))) ∧
      coracle = Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ st.compileOracle ∧
      Compiler.Backend.WordSimp.gcFunConstOk st.gcFun →
    ∃ perm' : Nat → Nat → Nat,
      let (res, rst) := evaluate prog { st with permute := perm' }
      if res = some .error then True
      else
        let (res1, rst1) := evaluate prog { st with code := l, compileOracle := coracle, compile := cc }
        res1 = res ∧ codeRel rst.code rst1.code ∧ sptDomain rst.code = sptDomain rst1.code ∧
          rst1 = { rst with
            code := rst1.code
            compileOracle :=
              Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ rst.compileOracle
            compile := cc }

/-- Every leaf statement satisfies the motive, with the identity permutation
    (Flapjack factoring of the leaf `Resume` cases). -/
theorem compileSingleCorrectAt_leaf {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (prog : WordLangProgHOL (BitVec width))
    (hp : cscLeaf prog = true) (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co prog st := by
  rintro l coracle cc ⟨hrel, hdom, -, hco, -⟩
  refine ⟨st.permute, ?_⟩
  rcases hrun : evaluate prog st with ⟨res, rst⟩
  dsimp only
  split
  · trivial
  have hmem : ∀ n, sptMem n l = sptMem n st.code := fun n => (congrFun hdom n).symm
  have hself := evaluate_tgt_frame st.code st.compileOracle st.compile st (fun _ => rfl) prog hp
  have hst : tgtState st.code st.compileOracle st.compile st = st := rfl
  rw [hst, hrun] at hself
  have hrst : rst = tgtState st.code st.compileOracle st.compile rst := (Prod.mk.inj hself).2
  have hcode : rst.code = st.code := by rw [hrst]; rfl
  have horacle : rst.compileOracle = st.compileOracle := by rw [hrst]; rfl
  have htgt := evaluate_tgt_frame l coracle cc st hmem prog hp
  rw [hrun] at htgt
  rw [show ({ st with code := l, compileOracle := coracle, compile := cc } :
      WordSemStateFiniteExact width C F) = tgtState l coracle cc st from rfl, htgt]
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [hcode]; exact hrel
  · rw [hcode]; exact hdom
  · rw [hco, horacle]; rfl

/-- HOL `compile_single_correct`, `Skip` case (`word_to_wordProofScript.sml:294-296`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Skip {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.skip : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Move` case (`word_to_wordProofScript.sml:298-301`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Move {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (priority : Nat) (moves : List (Nat × Nat))
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.move priority moves : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Inst` case (`word_to_wordProofScript.sml:303-306`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Inst {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (i : WordLangInst (BitVec width))
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.inst i : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Assign` case (`word_to_wordProofScript.sml:308-311`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Assign {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (name : Nat) (value : WordLangExpHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.assign name value : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Get` case (`word_to_wordProofScript.sml:313-316`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Get {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (destination : Nat) (store : WordStoreHOL)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.get destination store : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Set` case (`word_to_wordProofScript.sml:318-321`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Set {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (store : WordStoreHOL) (value : WordLangExpHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.set store value : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Store` case (`word_to_wordProofScript.sml:323-326`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Store {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (address : WordLangExpHOL (BitVec width)) (value : Nat)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.store address value : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Alloc` case (`word_to_wordProofScript.sml:750-765`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Alloc {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (destination : Nat) (cutsets : WordLangCutsetsHOL)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.alloc destination cutsets : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `StoreConsts` case (`word_to_wordProofScript.sml:767-769`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_StoreConsts {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (a b c d : Nat) (ws : List (Bool × BitVec width))
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.storeConsts a b c d ws : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Raise` case (`word_to_wordProofScript.sml:771-773`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Raise {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (exception : Nat)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.raise exception : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Return` case (`word_to_wordProofScript.sml:775-777`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Return {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (label : Nat) (values : List Nat)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.return label values : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Break` case (`word_to_wordProofScript.sml:779-782`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Break {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (label : Nat)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.break label : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Continue` case (`word_to_wordProofScript.sml:784-787`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Continue {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (label : Nat)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.continue label : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `Tick` case (`word_to_wordProofScript.sml:789-791`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_Tick {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.tick : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `OpCurrHeap` case (`word_to_wordProofScript.sml:793-795`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_OpCurrHeap {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (operator : BinOp) (destination source : Nat)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.opCurrHeap operator destination source : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `LocValue` case (`word_to_wordProofScript.sml:797-799`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_LocValue {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (destination source : Nat)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.locValue destination source : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `CodeBufferWrite` case (`word_to_wordProofScript.sml:824-826`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_CodeBufferWrite {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (address value : Nat)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.codeBufferWrite address value : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `DataBufferWrite` case (`word_to_wordProofScript.sml:828-830`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_DataBufferWrite {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (address value : Nat)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.dataBufferWrite address value : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `FFI` case (`word_to_wordProofScript.sml:832-834`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_FFI {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (function : Flapjack.Basis.Pure.MlString.MlString) (configuration configurationLength array arrayLength : Nat) (live : WordLangCutsetsHOL)
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.ffi function configuration configurationLength array arrayLength live : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

/-- HOL `compile_single_correct`, `ShareInst` case (`word_to_wordProofScript.sml:836-847`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct_ShareInst {width : Nat} [NeZero width] {C F : Type} (tt : Bool)
    (kk aa : Nat) (co : AsmConfigExact width) (operator : WordMemOp) (name : Nat) (address : WordLangExpHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F) :
    CompileSingleCorrectAt tt kk aa co (.shareInst operator name address : WordLangProgHOL (BitVec width)) st :=
  compileSingleCorrectAt_leaf tt kk aa co _ rfl st

end Flapjack.Compiler.Backend.WordToWord
