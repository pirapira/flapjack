import Flapjack.CrepeCalleeParameterContextRelation
import Flapjack.CompileParamVarsRelation

/-!
Compiler-side construction of the callee parameter records used by the
source-order state relation.

The source declaration stores a shape with each formal name, while the
compiled function stores the corresponding flattened slots.  This helper
packages source values with exactly that compiler-generated metadata.
-/

namespace Flapjack

def compileCalleeParameterList (params : List (VarName × Shape))
    (values : List (PanValue α)) (offset : Nat) : List (CalleeParameter α) :=
  match params, values with
  | (name, shape) :: params, value :: values =>
      { name := name
        shape := shape
        slots := (List.range (Shape.shapeSize shape)).map (fun index => offset + index)
        value := value
        values := panValueFlatWords value } ::
        compileCalleeParameterList params values
          (offset + Shape.shapeSize shape)
  | _, _ => []

theorem compileCalleeParameterList_metadata
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length) :
    (compileCalleeParameterList params values offset).map
        (fun parameter =>
          (parameter.name, (parameter.shape, parameter.slots))) =
      (compileParamVars params offset).1 := by
  induction params generalizing values offset with
  | nil =>
      cases values with
      | nil => simp [compileCalleeParameterList, compileParamVars]
      | cons value values => simp at hlength
  | cons param params ih =>
      cases param with
      | mk name shape =>
          cases values with
          | nil => simp at hlength
          | cons value values =>
              have htail : params.length = values.length := by
                simpa using hlength
              simp only [compileCalleeParameterList, compileParamVars,
                List.map_cons]
              rw [ih values (offset + Shape.shapeSize shape) htail]

theorem compileCalleeParameterList_flattened_slots
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length) :
    (compileCalleeParameterList params values offset).flatMap
        CalleeParameter.slots =
      (compileParamVars params offset).2.1 := by
  induction params generalizing values offset with
  | nil =>
      cases values with
      | nil => simp [compileCalleeParameterList, compileParamVars]
      | cons value values => simp at hlength
  | cons param params ih =>
      cases param with
      | mk name shape =>
          cases values with
          | nil => simp at hlength
          | cons value values =>
              have htail : params.length = values.length := by
                simpa using hlength
              simp only [compileCalleeParameterList, compileParamVars,
                List.flatMap_cons]
              rw [ih values (offset + Shape.shapeSize shape) htail]

theorem foldCalleeParameterContextAppend_empty_compile
    [OfNat α 0]
    (params : List (VarName × Shape)) (values : List (PanValue α))
    (offset : Nat) (hlength : params.length = values.length) :
    (foldCalleeParameterContextAppend
      ({ vars := [], functions := [], exceptions := [], maxVar := 0,
          bytesInWord := 0 } : CompileContext α)
      (compileCalleeParameterList params values offset)).vars =
      (compileParamVars params offset).1 := by
  rw [foldCalleeParameterContextAppend_eq]
  simp [compileCalleeParameterList_metadata params values offset hlength]

end Flapjack
