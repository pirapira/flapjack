import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.LoopToWord.CompFuncExact
import Flapjack.Pancake.Semantics.LoopSemStateExact
import Flapjack.Compiler.Backend.Semantics.WordSem.State

/-!
# `loop_to_wordProof` globals relation over the exact finite-map carriers

This is the exact port of `loop_to_wordProofScript.sml:27-30`'s
`globals_rel_def`. The source map is the `loopSem` state field
`5 word |-> word_loc`; the target is `wordSem`'s `store_name |-> word_loc`.
The target key is exactly `Temp n` from the imported `stackLang$store_name`
carrier. The relation is intentionally one-way and requires equality of the
stored `word_loc`; it makes no claim for target-only store entries. Both
finite-map arguments use the canonical `HolFiniteMapExact` rendering, and the
word payload uses the reviewed positive-width `BitVec` rendering.
-/

namespace Flapjack

/-- Exact HOL `globals_rel_def` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:27-30`:
every source global `(n,v)` must be present with the same value at the
WordSem `Temp n` key. Extra target store entries are unconstrained. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "globals_rel_def"
  (fmap_as_finite_support_relation := [g1, g2]) (words_as_type_indexed_bitvec)]
def loopToWordGlobalsRelHOLExact {width : Nat} [NeZero width]
    (g1 : HolFiniteMapExact (BitVec 5) (WordLocW width))
    (g2 : HolFiniteMapExact WordStoreHOL (WordLocW width)) : Prop :=
  ∀ n v, g1.lookup n = some v → g2.lookup (.temp n) = some v

/-- Exact HOL `globals_rel_intro` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:138-144`. It exposes the
same one-way lookup implication as `globals_rel_def`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "globals_rel_intro"
  (fmap_as_finite_support_relation := [g1, g2]) (words_as_type_indexed_bitvec)]
theorem loopToWordGlobalsRelIntroHOLExact {width : Nat} [NeZero width]
    (g1 : HolFiniteMapExact (BitVec 5) (WordLocW width))
    (g2 : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    loopToWordGlobalsRelHOLExact g1 g2 →
      ∀ n v, g1.lookup n = some v → g2.lookup (.temp n) = some v := by
  intro h n v hLookup
  exact h n v hLookup

/-- Exact HOL `code_rel_def` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:33-39`: every source code
entry `(params, body)` reached by `name` must be compiled to
`(LENGTH params + 1, comp_func name params body)` in the target code table,
and the parameter list must have no duplicates. The source code carrier is the
`loopSem` state's `funname |-> (varname list # prog)` as a reviewed
`Spt`, the target carrier is `wordSem`'s code `Spt` of
`Nat × WordLangProgHOL`, and the compiled body uses the exact
`loopToWordCompFuncHOL` port of HOL `comp_func`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "code_rel_def"
  (words_as_type_indexed_bitvec)]
def loopToWordCodeRelHOLExact {width : Nat} [NeZero width]
    (sourceCode : Spt (List Nat × HolLoopProg width))
    (targetCode : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ name params body,
    sptLookup name sourceCode = some (params, body) →
      sptLookup name targetCode =
          some (params.length + 1, loopToWordCompFuncHOL name params body) ∧
        params.Nodup

/-! Exact finite-support relation qualifier support: the two state carriers named
by `loopToWordStateRelHOLExact` own the finite-map fields `globals` and `store`.
These same-module re-exports make their canonical kernel-checked roundtrips
available to the tag checker without declaring another carrier. -/
namespace LoopToWordStateRelWitnesses

theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopToWordStateRelWitnesses

/-- Exact HOL `state_rel_def` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:41-52`, over the exact
`loopSem` and `wordSem` state carriers. It preserves the shared memory,
domains, clock, endianness and FFI state; the target `store`'s `CurrHeap` and
`HeapLength` entries for the source base address and an existential length; the
top-address equation `top_addr = base_addr + 2w*len`; and the exact
`globals_rel`/`code_rel` relations. Only the eligible finite-map fields
`LoopSemStateFiniteExact.globals` and `WordSemStateFiniteExact.store` are named
by the qualifier; `code` is an `Spt` tree map, not a `|->` finite map.

The existential length retains HOL's word carrier as `∃ len : BitVec width`.
The same native word appears directly in both HeapLength and the top-address
equation; the width remains positive and the configuration and FFI types remain
independent. No natural-number witness or extra representation qualifier is
introduced. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
def loopToWordStateRelHOLExact {width : Nat} [NeZero width] {C F : Type}
    (source : LoopSemStateFiniteExact width F)
    (target : WordSemStateFiniteExact width C F) : Prop :=
  ∃ len : BitVec width,
    target.memory = source.memory ∧
      target.mdomain = source.mdomain ∧
      target.shMdomain = source.shMdomain ∧
      target.clock = source.clock ∧
      target.be = source.be ∧
      target.ffi = source.ffi ∧
      target.store.lookup .currHeap = some (.word source.baseAddr) ∧
      target.store.lookup .heapLength = some (.word len) ∧
      source.topAddr = source.baseAddr + (2 : BitVec width) * len ∧
      loopToWordGlobalsRelHOLExact source.globals target.store ∧
      loopToWordCodeRelHOLExact source.code target.code

/-- Exact HOL `code_rel_intro` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:145-152`: the defining
`code_rel` implication, exposing the target lookup result
`(params.length+1, comp_func name params body)` and the `ALL_DISTINCT params`
side condition. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "code_rel_intro"
  (words_as_type_indexed_bitvec)]
theorem loopToWordCodeRelIntroHOLExact {width : Nat} [NeZero width]
    (sourceCode : Spt (List Nat × HolLoopProg width))
    (targetCode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (h : loopToWordCodeRelHOLExact sourceCode targetCode) :
    ∀ name params body,
      sptLookup name sourceCode = some (params, body) →
        sptLookup name targetCode =
            some (params.length + 1, loopToWordCompFuncHOL name params body) ∧
          params.Nodup :=
  h

/-- Exact HOL `state_rel_intro` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:154-168`: the projections of
`state_rel` that HOL exposes, namely the shared memory, `mdomain`, clock,
endianness and FFI state, the target `CurrHeap` entry for the source base
address, and the `globals_rel`/`code_rel` relations. Of the eligible
finite-map fields only `LoopSemStateFiniteExact.globals` and
`WordSemStateFiniteExact.store` are named. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "state_rel_intro"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem loopToWordStateRelIntroHOLExact {width : Nat} [NeZero width] {C F : Type}
    (source : LoopSemStateFiniteExact width F)
    (target : WordSemStateFiniteExact width C F)
    (h : loopToWordStateRelHOLExact source target) :
    target.memory = source.memory ∧
      target.mdomain = source.mdomain ∧
      target.clock = source.clock ∧
      target.be = source.be ∧
      target.ffi = source.ffi ∧
      target.store.lookup .currHeap = some (.word source.baseAddr) ∧
      loopToWordGlobalsRelHOLExact source.globals target.store ∧
      loopToWordCodeRelHOLExact source.code target.code := by
  obtain ⟨_, hmem, hmdom, _, hclock, hbe, hffi, hcurr, _, _, hglob, hcode⟩ := h
  exact ⟨hmem, hmdom, hclock, hbe, hffi, hcurr, hglob, hcode⟩

/-- Exact HOL `state_rel_IMP`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:272-275`): the two states of
`state_rel` share their clock. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "state_rel_IMP"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem loopToWordStateRelImpClockHOLExact {width : Nat} [NeZero width] {C F : Type}
    (source : LoopSemStateFiniteExact width F)
    (target : WordSemStateFiniteExact width C F)
    (h : loopToWordStateRelHOLExact source target) :
    target.clock = source.clock := by
  obtain ⟨_, _, _, _, hclock, _, _, _, _, _, _, _⟩ := h
  exact hclock

/-- Exact HOL `state_rel_with_clock`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:1497-1501`): replacing both
clocks by the same `k` preserves `state_rel`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "state_rel_with_clock"
  (fmap_as_finite_support_relation :=
    [LoopSemStateFiniteExact.globals, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem loopToWordStateRelWithClockHOLExact {width : Nat} [NeZero width] {C F : Type}
    (source : LoopSemStateFiniteExact width F)
    (target : WordSemStateFiniteExact width C F) (k : Nat)
    (h : loopToWordStateRelHOLExact source target) :
    loopToWordStateRelHOLExact { source with clock := k } { target with clock := k } := by
  obtain ⟨len, hmem, hmdom, hshm, _, hbe, hffi, hcurr, hhlen, htop, hglob, hcode⟩ := h
  exact ⟨len, hmem, hmdom, hshm, rfl, hbe, hffi, hcurr, hhlen, htop, hglob, hcode⟩

end Flapjack
