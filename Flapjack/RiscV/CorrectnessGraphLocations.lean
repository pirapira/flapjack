import Flapjack.RiscV.AllocatorCorrectness

/-!
# Graph-allocation source locations

Graph colouring stores the source-to-node inverse map separately from the
location map consumed by Word-to-Stack.  This small theorem makes the
conversion executable and proves that every source represented by an inverse
entry receives a corresponding physical or stack location.
-/

namespace Flapjack

theorem wordGraphLocations_lookup_of_fromNode
    (allocation : WordGraphAllocation) (colours stackStart source node : Nat)
    (hnode : lookupNatInfo node allocation.bijection.fromNode = some source) :
    ∃ location,
      lookupNatInfo source (wordGraphLocations allocation colours stackStart) =
        some location := by
  have go : ∀ entries : List (Nat × Nat),
      lookupNatInfo node entries = some source →
        ∃ location,
          lookupNatInfo source
              (entries.map (fun entry =>
                (entry.2, wordGraphLocationAt allocation colours stackStart entry.2))) =
            some location := by
    intro entries
    induction entries with
    | nil =>
        intro hentries
        simp [lookupNatInfo] at hentries
    | cons entry entries ih =>
      intro hentries
      rcases entry with ⟨entryNode, entrySource⟩
      by_cases hsame : entryNode = node
      · have hsource : entrySource = source := by
          simpa [lookupNatInfo, hsame] using hentries
        subst entrySource
        refine ⟨wordGraphLocationAt allocation colours stackStart source, ?_⟩
        simp [lookupNatInfo, hsame]
      · have htail :
            lookupNatInfo node entries = some source := by
          simpa [lookupNatInfo, hsame] using hentries
        have hresult := ih htail
        rcases hresult with ⟨location, hlocation⟩
        by_cases hsource : entrySource = source
        · subst entrySource
          exact ⟨wordGraphLocationAt allocation colours stackStart source, by
            simp [lookupNatInfo]⟩
        · exact ⟨location, by
            simpa [lookupNatInfo, hsource, hsame] using hlocation⟩
  simpa [wordGraphLocations] using go allocation.bijection.fromNode hnode

end Flapjack
