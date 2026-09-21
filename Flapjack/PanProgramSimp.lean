import Flapjack.PanProgramSemantics
import Flapjack.PanSimp

/-!
Counterpart of Cake's `decs_stcnames_compile_prog`
(`cakeml/pancake/proofs/pan_simpProofScript.sml:1334-1341`):

    !ctxt pan_code. decs_stcnames ctxt (compile_prog pan_code) =
                    decs_stcnames ctxt pan_code

Flapjack's `collectPanValueStructs` is the executable counterpart of Cake's
`decs_stcnames` (`cakeml/pancake/semantics/panSemScript.sml:839-859`), and
`panSimpDecls` is the counterpart of `pan_simp$compile_prog`.  Because
`pan_simp` rewrites only function bodies and leaves every other declaration
constructor untouched, it cannot change the struct-name context that
`collectPanValueStructs` accumulates. -/

namespace Flapjack

/-- Cons equation for `collectPanValueStructs`, mirroring Cake's
    `decs_stcnames_def`. -/
theorem collectPanValueStructs_cons (declaration : Decl α) (declarations : List (Decl α))
    (context : StructContext) :
    collectPanValueStructs (declaration :: declarations) context =
      (match declaration with
       | .name name fields =>
           if (lookupInfo name context).isSome then none
           else if !(fields.map (fun field => field.1)).Nodup then none
           else if !fields.all (fun field => isWfShape context field.2) then none
           else collectPanValueStructs declarations
                  ((name, panValueDeclStructInfo context fields) :: context)
       | _ => collectPanValueStructs declarations context) := by
  cases declaration <;> rw [collectPanValueStructs.eq_def]

/-- Cake's `decs_stcnames_compile_prog`: `pan_simp` preserves the
    struct-name context collected from a declaration list. -/
theorem collectPanValueStructs_panSimpDecls (declarations : List (Decl α))
    (context : StructContext) :
    collectPanValueStructs (panSimpDecls declarations) context =
      collectPanValueStructs declarations context := by
  rw [panSimpDecls_eq_map]
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration declarations ih =>
      simp only [List.map_cons]
      cases declaration <;>
        simp [panSimpDecl, collectPanValueStructs_cons, ih]

end Flapjack
