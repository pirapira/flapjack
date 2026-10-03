import Flapjack.Pancake.Proofs.PanStructs.CompileShapeN
import Flapjack.Pancake.Proofs.PanStructs.CompileShapeExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompiledShapesWf
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanStructs.CompileShapeExact
/-- Flapjack infrastructure: the single-shape projection of the mutual compiler
induction, supporting the full original conjunction below. -/
private theorem compiledWf {α : Type} (structs : List (MlS × α)) :
    ∀ (context : List (MlS × List (MlS × ShapeHOL))) (shape : ShapeHOL),
      isWfShapeExactHOL structs (compileShapeExact context shape) = true := by
  intro context shape
  induction context, shape using compileShapeExact.induct
    (motive2 := fun context shapes =>
      isWfShapesExactHOL structs (compileShapesExact context shapes) = true) with
  | case1 context => simp only [compileShapeExact, isWfShapeExactHOL]
  | case2 context shapes ih => simpa only [compileShapeExact, isWfShapeExactHOL] using ih
  | case3 context name key fields suffix hdrop ih =>
    rw [compileShapeExact]
    split
    · rename_i key2 fields2 suffix2 h2
      have he := hdrop.symm.trans h2
      cases he
      exact ih
    · rename_i h2
      rw [hdrop] at h2
      cases h2
  | case4 context name hdrop =>
    rw [compileShapeExact]
    split
    · rename_i key fields suffix h2
      rw [hdrop] at h2
      cases h2
    · rfl
  | case5 context => simp only [compileShapesExact, isWfShapesExactHOL]
  | case6 context shape shapes ih1 ih2 =>
    simp only [compileShapesExact, isWfShapesExactHOL, ih1, ih2, Bool.and_self]
/-- Both original compiled-shape well-formedness conjuncts, for arbitrary
payloads in the target struct context and the original fields-only compile
context. Compilation removes named struct shapes without any source-WF premise. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "is_wf_shape_compile_shape"]
theorem isWfShapeCompileShape {α : Type} (structs : List (MlS × α)) :
    (∀ (context : List (MlS × List (MlS × ShapeHOL))) (shape : ShapeHOL),
      isWfShapeExactHOL structs (compileShapeExact context shape) = true) ∧
    (∀ (context : List (MlS × List (MlS × ShapeHOL))) (shapes : List ShapeHOL),
      ∀ shape ∈ compileShapesExact context shapes, isWfShapeExactHOL structs shape = true) := by
  refine ⟨compiledWf structs, ?_⟩
  intro context shapes shape hmem
  rw [Flapjack.Pancake.Proofs.PanStructs.CompileShapeExact.compileShapesExact_eq_map] at hmem
  rcases List.mem_map.mp hmem with ⟨original, _, rfl⟩
  exact compiledWf structs context original
end Flapjack.Pancake.Proofs.PanStructs.CompiledShapesWf
