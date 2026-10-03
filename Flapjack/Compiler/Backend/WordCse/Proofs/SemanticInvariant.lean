import Flapjack.Compiler.Backend.WordCse.Proofs.WellFormedData
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack WordSemStateFiniteExact

namespace SemanticInvariantCarrier

/-- Canonical full-state map roundtrip, re-exported from the owning WordSem
carrier. The native knowledge carrier is not duplicated or translated. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticInvariantCarrier

/-- All eight original semantic knowledge conjuncts, over the faithful total
WordSem evaluator and full state. Arithmetic and memory evaluations retain
their original pair equations and post-state; no target execution, successful
conversion, opcode restriction or output relation is added. The imported
evaluator's declaration closure inherits the existing rational-cut IEEE real
rendering assumption (docs/SOUNDNESS.md item 8); the manifest records that
dependency for this predicate and its consumers. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "sem_inv_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
def semInv {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (state : WordSemStateFiniteExact width C F) : Prop :=
  (∀ (register value : Nat),
    sptLookup register data.toCanonical = some value →
      getVar register state = getVar value state) ∧
  (∀ (register value : Nat),
    sptLookup register data.toLatest = some value →
      getVar register state = getVar value state) ∧
  (∀ (destination : Nat) (constant : BitVec width) (value : Nat),
    Misc.BalancedMap.lookup listCmp (instToNumList (.const destination constant)) data.instrsMem = some value →
      sptLookup value state.locals = some (.word constant)) ∧
  (∀ (operation : Compiler.Encoders.Asm.HolArith width) (value : Nat),
    Misc.BalancedMap.lookup listCmp (instToNumList (.arith operation)) data.instrsMem = some value →
      ∃ word : WordLocW width, getVar value state = some word ∧
        evaluate (.inst (.arith operation.toWordLangArith)) state =
          (none, setVar (firstRegOfArith operation) word state)) ∧
  (∀ (operator : BinOp) (source value : Nat),
    Misc.BalancedMap.lookup listCmp (opCurrHeapToNumList operator source) data.instrsMem = some value →
      ∃ word : WordLocW width,
        wordExp state (.op operator [.var source, .lookup .currHeap]) = some word ∧
        getVar value state = some word) ∧
  (∀ (label value : Nat),
    Misc.BalancedMap.lookup listCmp [48, label] data.instrsMem = some value →
      sptLookup value state.locals = some (.loc label 0)) ∧
  (∀ (store : WordStoreHOL) (value : Nat),
    data.getsMem.lookup store = some value →
      ∃ word : WordLocW width, state.store.lookup store = some word ∧
        getVar value state = some word) ∧
  (∀ (operator : Compiler.Encoders.Asm.HolMemop) (address : Nat)
      (offset : BitVec width) (value : Nat),
    isStore operator = false ∧
      Misc.BalancedMap.lookup listCmp (loadToNumList operator address offset) data.loadsMem = some value →
      ∃ word : WordLocW width, getVar value state = some word ∧
        ∀ destination : Nat,
          evaluate (.inst (.mem operator destination (.addr address offset))) state =
            (none, setVar destination word state))

/-- Original combined invariant, retaining the complete syntactic and
semantic predicates over the same original word dimension and knowledge. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
def dataInv {width : Nat} [NeZero width] {C : Type} {F : Type}
    (data : Knowledge) (state : WordSemStateFiniteExact width C F) : Prop :=
  wfData width data ∧ semInv data state

/-- Original non-vacuous initializer: empty knowledge satisfies the complete
combined invariant for every faithful WordSem state, without run premises. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_empty"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem dataInvEmpty {width : Nat} [NeZero width] {C : Type} {F : Type}
    (state : WordSemStateFiniteExact width C F) : dataInv emptyData state := by
  simp [dataInv, wfData, semInv, emptyData, Misc.BalancedMap.empty, Misc.BalancedMap.lookup,
    Misc.BalancedMap.invariant]

end Flapjack.Compiler.Backend.WordCse
