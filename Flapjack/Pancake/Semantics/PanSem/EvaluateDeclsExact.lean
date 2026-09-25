/-
EXACT DECLARATION EVALUATION (flapjack-pxn.18.3.6.9.22).

Function-backed rendering of HOL `evaluate_decls_def`
(`cakeml/pancake/semantics/panSemScript.sml:814-837`) over `PanSemStateExact`,
the exact `DeclHOL` syntax, and the exact `ValueHOL` values. The state carrier
admits arbitrary lookup functions instead of HOL finite-map fields, so this
definition has no `@[hol]` tag. Every lookup is `=`-keyed (`MlString` derives
`DecidableEq`); the shape comparison goes through `shapeEqHOL` (whose `= true`
reading is proved exact in `IsValidValueExact.lean`); the declaration bodies are
evaluated with the untagged function-backed `evalHOLExact` under empty locals;
the well-formedness checks reuse the tagged exact `isWfShapeExactHOL`
(`is_wf_shape_def`); the struct context and the code/eshapes maps are updated
`=`-keyed.

HOL clauses (`panSemScript.sml:814-837`):

```
evaluate_decls s []                    = SOME s
evaluate_decls s (Name nm flds::ds)    = evaluate_decls s ds
evaluate_decls s (Decl sh v e::ds)     =
  case eval (s with locals := FEMPTY) e of
    SOME res => if sh = shape_of res
                then evaluate_decls (s with globals := s.globals |+ (v,res)) ds
                else NONE
  | NONE => NONE
evaluate_decls s (Function fi::ds)     =
  if EVERY ((is_wf_shape s.structs) o SND) fi.params /\ is_wf_shape s.structs fi.return
  then evaluate_decls (s with code := s.code |+ (fi.name,(fi.params,(fi.body,fi.return)))) ds
  else NONE
evaluate_decls s (ExnDecl eid sh::ds)  =
  if FLOOKUP s.eshapes eid = NONE /\ is_wf_shape s.structs sh
  then evaluate_decls (s with eshapes := s.eshapes |+ (eid,sh)) ds
  else NONE
```

The direct original-HOL EVAL rows for these clauses are in
`scripts/hol-probes/pan_evaluate_decls_probe.out` (registered in
`scripts/hol-probes/regenerate.sh:194`) and are reproduced by
`Flapjack/Test/PanSemEvaluateDeclsExactParity.lean`.
-/
import Flapjack.Pancake.Semantics.PanSem.EvalExact

namespace Flapjack

open Flapjack.Pancake.PanLang
  (MlS ShapeHOL ExpHOL DeclHOL ProgHOL isWfShapeExactHOL)

/-- `=`-keyed global update (`s.globals |+ (name, value)`). -/
abbrev evaluateDeclsSetGlobal {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS) (value : ValueHOL width) :
    PanSemStateExact width σ :=
  { state with globals :=
      fun current => if current = name then some value else state.globals current }

/-- `=`-keyed code update (`s.code |+ (name, (params, body, return))`). -/
abbrev evaluateDeclsSetCode {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS)
    (params : List (MlS × ShapeHOL)) (body : ProgHOL width) (returnShape : ShapeHOL) :
    PanSemStateExact width σ :=
  { state with code :=
      fun current =>
        if current = name then some (params, body, returnShape) else state.code current }

/-- `=`-keyed exception-shape update (`s.eshapes |+ (eid, sh)`). -/
abbrev evaluateDeclsSetEshape {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (exceptionName : MlS) (shape : ShapeHOL) :
    PanSemStateExact width σ :=
  { state with eshapes :=
      fun current => if current = exceptionName then some shape else state.eshapes current }

/-- Function-backed rendering of HOL `evaluate_decls_def` (`panSemScript.sml:814-837`).
    Kept untagged because whole-state map fields are unrestricted functions
    rather than finite maps. -/
def evaluateDeclsHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] :
    List (DeclHOL width) → Option (PanSemStateExact width σ)
  | [] => some state
  | .name _ _ :: declarations => evaluateDeclsHOLExact state declarations
  | .decl shape name expression :: declarations =>
      match evalHOLExact { state with locals := fun _ => none } expression with
      | some value =>
          if shapeEqHOL shape (shapeOfHOLExact value) then
            evaluateDeclsHOLExact (evaluateDeclsSetGlobal state name value) declarations
          else none
      | none => none
  | .function declaration :: declarations =>
      if declaration.params.all
            (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
          isWfShapeExactHOL state.structs declaration.returnShape then
        evaluateDeclsHOLExact
          (evaluateDeclsSetCode state declaration.name declaration.params
            declaration.body declaration.returnShape)
          declarations
      else none
  | .exnDecl exceptionName shape :: declarations =>
      if (state.eshapes exceptionName).isNone && isWfShapeExactHOL state.structs shape then
        evaluateDeclsHOLExact
          (evaluateDeclsSetEshape state exceptionName shape)
          declarations
      else none

end Flapjack
