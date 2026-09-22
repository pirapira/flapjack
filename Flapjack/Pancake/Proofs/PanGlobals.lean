import Flapjack.HolRef
import Flapjack.PanGlobalsSemantics

/-!
Lean counterparts of the shape well-formedness results in Cake's
`pan_globalsProofScript.sml`. The declarations below retain Flapjack's
start-function entry point and are mapped to the corresponding HOL theorems.
-/

namespace Flapjack

/-- If declaration evaluation succeeds, the start-function entry point emits
    only function declarations with well-formed parameter and return shapes. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_shape_wf"]
theorem globalCompileTopForStart_shapes_wf
    [BEq String] [LawfulBEq String] [Add α] [Mul α]
    [BEq α] [OfNat α 0] [OfNat α 1] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (bytesInWord : α) (fromNat : Nat → α) (start : FunName)
    (compiled : List (Decl α))
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state')
    (hcompile : globalCompileTopForStart bytesInWord fromNat declarations start =
      some compiled) :
    compiled.all (panDeclShapesWellFormed structs) = true := by
  have hsource := evalPanValueDeclarationsWithStructs_all_shapes structs state
    state' declarations memoryAccess heval
  unfold globalCompileTopForStart at hcompile
  cases hfind : globalFindFunction start declarations with
  | none => simp [hfind] at hcompile
  | some entry =>
      simp only [hfind, Option.some.injEq] at hcompile
      subst hcompile
      have hwf := evalPanValueDeclarationsWithStructs_functions_wf structs state
        state' declarations memoryAccess heval
        (globalFindFunction_mem start declarations entry hfind)
      have hresort := globalResortDecls_all_shapes structs declarations hsource
      have hrenamed : (globalRenameDecls start (globalNewMainName declarations)
          (globalResortDecls declarations)).all
          (panDeclShapesWellFormed structs) = true :=
        globalRenameDecls_all_of_predicate start (globalNewMainName declarations)
          (panDeclShapesWellFormed structs) (globalResortDecls declarations)
          (List.all_eq_true.mpr
            (fun declaration _ => panDeclShapesWellFormed_or_function structs declaration))
          (globalResortDecls_all_of_renamed structs start
            (globalNewMainName declarations) declarations hresort)
      refine globalCompileDecs_result_shapes_wf structs _ _ _ ?_ ?_
      · simp [panDeclShapesWellFormed, panFunctionShapesWellFormed, hwf.1, hwf.2]
      · simpa [panDeclShapesWellFormed, panFunctionShapesWellFormed] using hrenamed

/-- Empty-struct-context instance of the start-function shape invariant. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_shape_wf_nil"]
theorem globalCompileTopForStart_shapes_wf_nil
    [BEq String] [LawfulBEq String] [Add α] [Mul α]
    [BEq α] [OfNat α 0] [OfNat α 1] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (bytesInWord : α) (fromNat : Nat → α) (start : FunName)
    (compiled : List (Decl α))
    (heval : evalPanValueDeclarationsWithStructs ([] : StructContext) state
      declarations memoryAccess = some state')
    (hcompile : globalCompileTopForStart bytesInWord fromNat declarations start =
      some compiled) :
    compiled.all (panDeclShapesWellFormed ([] : StructContext)) = true :=
  globalCompileTopForStart_shapes_wf ([] : StructContext) state state'
    declarations memoryAccess bytesInWord fromNat start compiled heval hcompile

end Flapjack
