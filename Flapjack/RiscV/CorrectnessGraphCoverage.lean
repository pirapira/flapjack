import Flapjack.RiscV.CorrectnessGraphLocations
import Flapjack.RiscV.OracleAllocator

/-!
# Full-SSA graph coverage

The graph allocator stores a source-to-node bijection while constructing the
clash graph.  The executable allocator already exposes coloring checks, but a
location-aware lowering also needs the complementary coverage fact: every
name mentioned by a clash tree has a node in that bijection.  These lemmas
keep that fact independent of the allocator algorithm itself.
-/

namespace Flapjack

open RiscV

theorem wordClashTreeBijection_lookup_preserves
    (tree : WordClashTree) (bijection : WordBijection) :
    ∀ name node,
      lookupNatInfo name bijection.toNode = some node →
      lookupNatInfo name
        (wordClashTreeBijection tree bijection).toNode = some node := by
  induction tree generalizing bijection with
  | delta writes reads =>
      intro name node hlookup
      simpa [wordClashTreeBijection] using
        wordListRemap_lookup_preserves (writes ++ reads) bijection name node hlookup
  | set names =>
      intro name node hlookup
      simpa [wordClashTreeBijection] using
        wordListRemap_lookup_preserves names bijection name node hlookup
  | branch live thenBranch elseBranch ihThen ihElse =>
      intro name node hlookup
      have hthen := ihThen bijection name node hlookup
      have helse := ihElse (wordClashTreeBijection thenBranch bijection)
        name node hthen
      cases live with
      | none => simpa [wordClashTreeBijection] using helse
      | some names =>
          simpa [wordClashTreeBijection] using
            wordListRemap_lookup_preserves names
            (wordClashTreeBijection elseBranch
              (wordClashTreeBijection thenBranch bijection))
            name node helse
  | seq first second ihFirst ihSecond =>
      intro name node hlookup
      have hsecond := ihSecond bijection name node hlookup
      simpa [wordClashTreeBijection] using
        ihFirst (wordClashTreeBijection second bijection) name node hsecond

theorem wordClashTreeBijection_maps_names
    (tree : WordClashTree) (bijection : WordBijection) :
    ∀ name, name ∈ wordClashTreeNames tree →
      ∃ node, lookupNatInfo name
        (wordClashTreeBijection tree bijection).toNode = some node := by
  induction tree generalizing bijection with
  | delta writes reads =>
      intro name hname
      have hname' : name ∈ writes ++ reads := by
        simpa [wordClashTreeNames] using hname
      simpa [wordClashTreeBijection] using
        wordListRemap_lookup_of_mem (writes ++ reads) bijection name hname'
  | set names =>
      intro name hname
      have hname' : name ∈ names := by
        simpa [wordClashTreeNames] using hname
      simpa [wordClashTreeBijection] using
        wordListRemap_lookup_of_mem names bijection name hname'
  | branch live thenBranch elseBranch ihThen ihElse =>
      cases live with
      | none =>
          intro name hname
          have hname' : name ∈ wordClashTreeNames thenBranch ++
              wordClashTreeNames elseBranch := by
            simpa [wordClashTreeNames] using hname
          rcases List.mem_append.mp hname' with hthen | helse
          · rcases ihThen bijection name hthen with ⟨node, hnode⟩
            exact ⟨node, by
              simpa [wordClashTreeBijection] using
                wordClashTreeBijection_lookup_preserves elseBranch
                  (wordClashTreeBijection thenBranch bijection)
                  name node hnode⟩
          · rcases ihElse (wordClashTreeBijection thenBranch bijection)
                name helse with ⟨node, hnode⟩
            exact ⟨node, by simpa [wordClashTreeBijection] using hnode⟩
      | some live =>
          intro name hname
          have hname' : name ∈ (live ++ wordClashTreeNames thenBranch) ++
              wordClashTreeNames elseBranch := by
            simpa [wordClashTreeNames] using hname
          rcases List.mem_append.mp hname' with hliveThen | helse
          · rcases List.mem_append.mp hliveThen with hlive | hthen
            · rcases wordListRemap_lookup_of_mem live
                (wordClashTreeBijection elseBranch
                  (wordClashTreeBijection thenBranch bijection)) name hlive with
              ⟨node, hnode⟩
              exact ⟨node, by simpa [wordClashTreeBijection] using hnode⟩
            · rcases ihThen bijection name hthen with ⟨node, hnode⟩
              have hnode' := wordClashTreeBijection_lookup_preserves
                elseBranch (wordClashTreeBijection thenBranch bijection)
                name node hnode
              have hfinal := wordListRemap_lookup_preserves live
                (wordClashTreeBijection elseBranch
                  (wordClashTreeBijection thenBranch bijection))
                name node hnode'
              exact ⟨node, by simpa [wordClashTreeBijection] using hfinal⟩
          · rcases ihElse (wordClashTreeBijection thenBranch bijection)
                name helse with ⟨node, hnode⟩
            have hfinal := wordListRemap_lookup_preserves live
              (wordClashTreeBijection elseBranch
                (wordClashTreeBijection thenBranch bijection))
              name node hnode
            exact ⟨node, by simpa [wordClashTreeBijection] using hfinal⟩
  | seq first second ihFirst ihSecond =>
      intro name hname
      have hname' : name ∈ wordClashTreeNames first ++
          wordClashTreeNames second := by
        simpa [wordClashTreeNames] using hname
      rcases List.mem_append.mp hname' with hfirst | hsecond
      · rcases ihFirst (wordClashTreeBijection second bijection) name hfirst with
          ⟨node, hnode⟩
        exact ⟨node, by simpa [wordClashTreeBijection] using hnode⟩
      · rcases ihSecond bijection name hsecond with ⟨node, hnode⟩
        exact ⟨node, by
          simpa [wordClashTreeBijection] using
            wordClashTreeBijection_lookup_preserves first
              (wordClashTreeBijection second bijection) name node hnode⟩

theorem wordAllocateGraph_maps_clash_names
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (moves : List (Nat × Nat))
    (colours stackStart : Nat) (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraph tree forced fixedSources moves colours stackStart =
      some allocation) :
    ∀ name, name ∈ wordClashTreeNames tree →
      ∃ node, lookupNatInfo name allocation.bijection.toNode = some node := by
  simp [wordAllocateGraph] at halloc
  rcases halloc with ⟨_, heq⟩
  cases heq
  intro name hname
  have hnode := wordClashTreeBijection_maps_names tree
    { toNode := [], fromNode := [], next := 0 } name hname
  simpa [wordInitRegAlloc, wordMkBijection] using hnode

theorem wordAllocateGraph_maps_clash_locations
    (tree : WordClashTree) (forced : List (Nat × Nat))
    (fixedSources : List Nat) (moves : List (Nat × Nat))
    (colours stackStart : Nat) (allocation : WordGraphAllocation)
    (halloc : wordAllocateGraph tree forced fixedSources moves colours stackStart =
      some allocation) :
    ∀ name, name ∈ wordClashTreeNames tree →
      ∃ location,
        lookupNatInfo name (wordGraphLocations allocation colours stackStart) =
          some location := by
  simp [wordAllocateGraph] at halloc
  rcases halloc with ⟨_, heq⟩
  cases heq
  intro name hname
  have hnode := wordClashTreeBijection_maps_names tree
    { toNode := [], fromNode := [], next := 0 } name hname
  rcases hnode with ⟨node, hnode⟩
  have hnode' : lookupNatInfo name (wordMkBijection tree).toNode = some node := by
    simpa [wordMkBijection] using hnode
  have hinverse := wordMkBijection_lookup_inverse tree name node hnode'
  apply wordGraphLocations_lookup_of_fromNode
  simpa [wordInitRegAlloc, wordMkBijection] using hinverse

theorem wordAllocateGraphFunctionWithEntryRenamed_maps_clash_names
    (parameters : List Nat) (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (renamedProgram : WordProg α)
    (halloc : wordAllocateGraphFunctionWithEntryRenamed parameters program
      fixedSources colours stackStart =
      some (state, renamedParameters, allocation, renamedProgram)) :
    ∀ name, name ∈ wordClashTreeNames
        (WordClashTree.seq (.set renamedParameters)
          (wordClashTree renamedProgram [])) →
      ∃ node, lookupNatInfo name allocation.bijection.toNode = some node := by
  simp [wordAllocateGraphFunctionWithEntryRenamed] at halloc
  rcases halloc with ⟨allocation', hgraph, rfl, rfl, rfl, rfl⟩
  exact wordAllocateGraph_maps_clash_names
    (WordClashTree.seq
      (.set (wordSsaRenameFunctionWithEntry parameters program).2.fst)
      (wordClashTree (wordSsaRenameFunctionWithEntry parameters program).2.snd []))
    (wordProgForcedClashes (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    fixedSources
      (wordProgPreferenceEdges (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    colours stackStart allocation' hgraph

end Flapjack
