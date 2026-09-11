import Flapjack.CrepeDeclarationRelation

/-!
Elementary facts about the compiler's generated local names.  These are
structural facts about the range-based allocation scheme and are shared by
declaration and temporary-assignment correctness proofs.
-/

namespace Flapjack

theorem crepDistinctNames_range_add (start count : Nat) :
    CrepDistinctNames ((List.range count).map (fun offset => start + offset)) := by
  have happend : ∀ (entries : List Nat) (value : Nat),
      CrepDistinctNames entries → value ∉ entries →
      CrepDistinctNames (entries ++ [value]) := by
    intro entries value
    induction entries generalizing value with
    | nil =>
        intro _ _
        simp [CrepDistinctNames]
    | cons head tail ih =>
        intro hdistinct hnot
        rcases hdistinct with ⟨hhead, htail⟩
        have hheadValue : head ≠ value := by
          intro heq
          apply hnot
          simp [heq]
        have htailNot : value ∉ tail := by
          intro hmem
          apply hnot
          simp [hmem]
        have hheadNot : head ∉ tail ++ [value] := by
          intro hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | hmem
          · exact hhead hmem
          · exact hheadValue hmem
        exact ⟨hheadNot, ih value htail htailNot⟩
  induction count with
  | zero =>
      simp [CrepDistinctNames]
  | succ count ih =>
      have hnot : start + count ∉
          (List.range count).map (fun offset => start + offset) := by
        intro hmem
        obtain ⟨offset, hoff, heq⟩ := List.mem_map.mp hmem
        have hofflt : offset < count := List.mem_range.mp hoff
        omega
      simpa [List.range_succ, List.map_append] using
        happend ((List.range count).map (fun offset => start + offset))
          (start + count) ih hnot

theorem crepDistinctNames_allocatedNames
    (context : CompileContext α) (shape : Shape) :
    CrepDistinctNames (allocatedNames context shape) := by
  simpa [allocatedNames] using
    crepDistinctNames_range_add (context.maxVar + 1) (Shape.shapeSize shape)

theorem crepDistinctNames_freshNames
    (context : CompileContext α) (count start : Nat) :
    CrepDistinctNames (freshNames context count start) := by
  simpa [freshNames] using
    crepDistinctNames_range_add (context.maxVar + start) count

theorem allocatedNames_length
    (context : CompileContext α) (shape : Shape) :
    (allocatedNames context shape).length = Shape.shapeSize shape := by
  simp [allocatedNames]

theorem freshNames_length
    (context : CompileContext α) (count start : Nat) :
    (freshNames context count start).length = count := by
  simp [freshNames]

end Flapjack
