import Flapjack.Compiler.Backend.WordCse.ProductionKnowledge
import Flapjack.Compiler.Backend.WordCse.Join
import Flapjack.Compiler.Backend.WordCse.Proofs.WfDataPreservation
import Flapjack.Compiler.Backend.WordCse.Proofs.IntersectionAccumulator
import Flapjack.Misc.Sptree.InterEq
import Std.Data.TreeMap.Lemmas

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Actual executed register intersection preserves native Spt lookup on every
key, including unrestricted source trees. Flapjack representation transport,
not a separately named HOL theorem or a supplied output correspondence. -/
theorem interEq_production_transport (first second : Spt Nat)
    (executedFirst executedSecond : WordCseRegMap)
    (firstRelated : ∀ key, sptLookup key first = executedFirst[key]?)
    (secondRelated : ∀ key, sptLookup key second = executedSecond[key]?) :
    ∀ key, sptLookup key (sptInterEq first second) =
      (wordCseInterEq executedFirst executedSecond)[key]? := by
  intro key
  rw [sptLookupInterEq, firstRelated key]
  simp only [wordCseInterEq, Std.TreeMap.getElem?_filter']
  cases h : executedFirst[key]? with
  | none => rfl
  | some value =>
    simp only [Option.filter_some, secondRelated key]
    by_cases equal : executedSecond[key]? = some value
    · simp [equal]
    · simp [equal]

/-- Both complete executed fact tables use the reviewed native intersection
lookup theorem with exactly its two original balanced-map invariants. -/
theorem bmInterEq_production_transport
    (first second : Misc.BalancedMap.Map (List Nat) Nat)
    (executedFirst executedSecond : WordCseFactMap)
    (firstInvariant : Misc.BalancedMap.invariant listCmp first)
    (secondInvariant : Misc.BalancedMap.invariant listCmp second)
    (firstRelated : ∀ key, Misc.BalancedMap.lookup listCmp key first = executedFirst[key]?)
    (secondRelated : ∀ key, Misc.BalancedMap.lookup listCmp key second = executedSecond[key]?) :
    ∀ key, Misc.BalancedMap.lookup listCmp key (bmInterEq first second) =
      (wordCseListInterEq executedFirst executedSecond)[key]? := by
  have : Std.TransCmp listCmp := by
    rw [listCmpFunctionEqStdCompare]
    infer_instance
  have : Std.LawfulEqCmp listCmp := by
    rw [listCmpFunctionEqStdCompare]
    infer_instance
  intro key
  have sameSome : ∀ value, Misc.BalancedMap.lookup listCmp key (bmInterEq first second) = some value ↔
      (wordCseListInterEq executedFirst executedSecond)[key]? = some value := by
    intro value
    rw [lookupBmInterEq first second key value ⟨firstInvariant, secondInvariant⟩,
      firstRelated key, secondRelated key]
    simp [wordCseListInterEq]
  cases native : Misc.BalancedMap.lookup listCmp key (bmInterEq first second) with
  | none =>
    cases executed : (wordCseListInterEq executedFirst executedSecond)[key]? with
    | none => rfl
    | some value =>
      have impossible := (sameSome value).mpr executed
      simp [native] at impossible
  | some value => exact ((sameSome value).mp native).symm

/-- A first-match association-list lookup commutes with filtering only when
its keys are unique. This input representation obligation is not an output
relation or an extra hypothesis on a tagged original HOL theorem. -/
private theorem lookupFilterUnique {Key : Type} [BEq Key] [LawfulBEq Key]
    (entries : List (Key × Nat)) (predicate : Key × Nat → Bool)
    (unique : (entries.map Prod.fst).Nodup) (key : Key) :
    (entries.filter predicate).lookup key =
      (entries.lookup key).filter (fun value => predicate (key,value)) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨headKey,value⟩
    have parts : headKey ∉ entries.map Prod.fst ∧ (entries.map Prod.fst).Nodup := by
      simpa using unique
    by_cases same : key = headKey
    · subst key
      have filteredAbsent : (entries.filter predicate).lookup headKey = none := by
        apply List.lookup_eq_none_iff.mpr
        intro pair present
        have absent : headKey ≠ pair.1 := by
          intro equal
          apply parts.1
          exact List.mem_map.mpr ⟨pair,List.mem_of_mem_filter present,equal.symm⟩
        simpa using absent
      cases kept : predicate (headKey,value) <;>
        simp [List.lookup,Option.filter_some,kept,filteredAbsent]
    · have different : (key == headKey) = false := beq_eq_false_iff_ne.mpr same
      cases kept : predicate (headKey,value) <;>
        simp [List.lookup,kept,different,ih parts.2]

/-- Full store-filter lookup transport, retaining the necessary input
unique-key condition on the native ordered association list. -/
theorem storeJoin_production_transport {width : Nat} [NeZero width]
    (first second : List (WordStoreHOL × Nat))
    (executedFirst executedSecond : WordCseRegMap)
    (unique : (first.map Prod.fst).Nodup)
    (firstRelated : ∀ store, first.lookup store =
      executedFirst[wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))]?)
    (secondRelated : ∀ store, second.lookup store =
      executedSecond[wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))]?) :
    ∀ store, (first.filter (fun entry => decide (second.lookup entry.1 = some entry.2))).lookup store =
      (executedFirst.filter (fun key value => executedSecond[key]? == some value))[
        wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))]? := by
  intro store
  rw [lookupFilterUnique _ _ unique, firstRelated store]
  simp only [Std.TreeMap.getElem?_filter']
  cases found : executedFirst[wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))]? with
  | none => rfl
  | some value =>
    simp only [Option.filter_some, secondRelated store]
    by_cases equal : executedSecond[wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))]? = some value
    · simp [equal]
    · simp [equal]

/-- Complete five-field branch-join correspondence for the actual executed
join. Premises are input representation/invariants only. Generated knowledge
invariant preservation and actual whole-pass adoption remain separate duties;
this untagged transport does not narrow a HOL compiler theorem. -/
theorem mergeData_production_transport {width : Nat} [NeZero width]
    (first second : Knowledge) (executedFirst executedSecond : WordCseKnowledge)
    (firstRelated : KnowledgeRel width first executedFirst)
    (secondRelated : KnowledgeRel width second executedSecond)
    (storesUnique : (first.getsMem.map Prod.fst).Nodup)
    (firstInstrs : Misc.BalancedMap.invariant listCmp first.instrsMem)
    (secondInstrs : Misc.BalancedMap.invariant listCmp second.instrsMem)
    (firstLoads : Misc.BalancedMap.invariant listCmp first.loadsMem)
    (secondLoads : Misc.BalancedMap.invariant listCmp second.loadsMem) :
    KnowledgeRel width (mergeData first second) (wordCseMergeData executedFirst executedSecond) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact interEq_production_transport _ _ _ _ firstRelated.1 secondRelated.1
  · intro key; rfl
  · exact storeJoin_production_transport _ _ _ _ storesUnique firstRelated.2.2.1 secondRelated.2.2.1
  · exact bmInterEq_production_transport _ _ _ _ firstInstrs secondInstrs firstRelated.2.2.2.1 secondRelated.2.2.2.1
  · exact bmInterEq_production_transport _ _ _ _ firstLoads secondLoads firstRelated.2.2.2.2 secondRelated.2.2.2.2

/-- Original well-formed knowledge supplies every join input obligation,
including ordered-store key uniqueness. No new producer invariant is assumed. -/
theorem mergeData_wf_production_transport {width : Nat} [NeZero width]
    (first second : Knowledge) (executedFirst executedSecond : WordCseKnowledge)
    (firstRelated : KnowledgeRel width first executedFirst)
    (secondRelated : KnowledgeRel width second executedSecond)
    (firstWellFormed : wfData width first) (secondWellFormed : wfData width second) :
    KnowledgeRel width (mergeData first second) (wordCseMergeData executedFirst executedSecond) := by
  exact mergeData_production_transport first second executedFirst executedSecond
    firstRelated secondRelated firstWellFormed.2.2.2.2.2.2.1
    firstWellFormed.2.2.2.2.2.2.2.1 secondWellFormed.2.2.2.2.2.2.2.1
    firstWellFormed.2.2.2.2.2.2.2.2.2.2 secondWellFormed.2.2.2.2.2.2.2.2.2.2

/-- Native transformed branch inputs inherit original whole-program
well-formedness. Relations are arm induction hypotheses, never an assumed
output join relation. This is production infrastructure, not a HOL port. -/
theorem transformedBranches_production_transport {width : Nat} [NeZero width]
    (data : Knowledge) (first second : WordLangProgHOL (BitVec width))
    (executedFirst executedSecond : WordCseKnowledge)
    (wellFormed : wfData width data)
    (firstRelated : KnowledgeRel width (wordCse data first).1 executedFirst)
    (secondRelated : KnowledgeRel width (wordCse data second).1 executedSecond) :
    KnowledgeRel width (mergeData (wordCse data first).1 (wordCse data second).1)
      (wordCseMergeData executedFirst executedSecond) := by
  exact mergeData_wf_production_transport _ _ _ _ firstRelated secondRelated
    (word_cse_wf_data first data wellFormed) (word_cse_wf_data second data wellFormed)

/-- Knowledge correspondence at the actual executed If call site. The only
recursive hypotheses relate the two independently transformed arms; original
whole-program well-formedness supplies their join invariants. No HOL tag is
attached to this Flapjack representation theorem. -/
theorem wordCseIf_production_transport {width : Nat} [NeZero width]
    (data : Knowledge) (executed : WordCseKnowledge)
    (operator : Cmp) (condition : Nat) (right : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (executedFirst executedSecond : WordProg (BitVec width))
    (wellFormed : wfData width data)
    (firstRelated : KnowledgeRel width (wordCse data first).1
      (wordCseProg executed executedFirst).2)
    (secondRelated : KnowledgeRel width (wordCse data second).1
      (wordCseProg executed executedSecond).2) :
    KnowledgeRel width (wordCse data (.ite operator condition right first second)).1
      (wordCseProg executed (.ite operator condition right executedFirst executedSecond)).2 := by
  simpa only [wordCse, wordCseProg] using
    transformedBranches_production_transport data first second _ _ wellFormed
      firstRelated secondRelated

end Flapjack.Compiler.Backend.WordCse
