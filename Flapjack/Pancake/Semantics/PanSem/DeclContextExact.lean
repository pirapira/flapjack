/-
Copyright (c) 2026 Flapjack contributors.

Exact HOL `panSem$decs_stcnames` over the MlString-keyed declaration carriers.

`cakeml/pancake/semantics/panSemScript.sml:839-856` defines

```
Definition decs_stcnames_def:
  decs_stcnames st_ctxt [] = SOME st_ctxt /\
  decs_stcnames st_ctxt (Name nm flds :: ds) =
    (case ALOOKUP st_ctxt nm of
     | SOME info => NONE
     | NONE =>
       if ALL_DISTINCT (MAP FST flds) then
         let shs = MAP SND flds in
         if EVERY (is_wf_shape st_ctxt) shs then
           let info = <|fields := flds; size := size_of_sh_with_ctxt st_ctxt (Comb shs)|>
           in decs_stcnames ((nm, info) :: st_ctxt) ds
         else NONE
       else NONE) /\
  decs_stcnames st_ctxt (Decl sh v e :: ds) = decs_stcnames st_ctxt ds /\
  decs_stcnames st_ctxt (Function fi :: ds) = decs_stcnames st_ctxt ds /\
  decs_stcnames st_ctxt (ExnDecl eid sh :: ds) = decs_stcnames st_ctxt ds
```

This module renders it over the exact HOL-shaped carriers `DeclHOL`,
`StructContextExact`, `StructInfoHOLExact`, `ShapeHOL` (`Flapjack.Pancake.PanLang`)
and reuses the exact helpers `structContextLookupHOL` (the `ALOOKUP`), `isWfShapeExactHOL`
(the `is_wf_shape` predicate) and `sizeOfShapeWithContextHOL` (the `size_of_sh_with_ctxt`
of `Comb shs`).  The result is a `StructContextExact` built from the same `(nm, info)`
entries as HOL, so the clause shapes and side conditions match the HOL definition
exactly; the tag is therefore attached to the Lean definition.
-/

import Flapjack.Pancake.PanLang.Decl
import Flapjack.HolRef

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Exact port of HOL `panSem$decs_stcnames` (`cakeml/pancake/semantics/panSemScript.sml:839`).

It scans a declaration list and accumulates the structure context: a `Name nm flds`
entry is admitted exactly when `nm` is not already present (`ALOOKUP` misses), the
field names are distinct (`ALL_DISTINCT (MAP FST flds)`), and every field shape is
well formed under the current context (`EVERY (is_wf_shape st_ctxt) shs`); the stored
`struct_info` has `fields := flds` and `size := size_of_sh_with_ctxt st_ctxt (Comb shs)`.
`Decl`, `Function` and `ExnDecl` entries are skipped and the scan continues.  A rejected
entry yields `NONE`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "decs_stcnames_def"]
def decsStcnamesHOLExact {width : Nat} [NeZero width] (context : StructContextExact) :
    List (DeclHOL width) → Option StructContextExact
  | [] => some context
  | .name struct fields :: rest =>
      match structContextLookupHOL struct context with
      | some _ => none
      | none =>
          if (fields.map (fun field => field.1)).Nodup then
            let shapes := fields.map (fun field => field.2)
            if shapes.all (fun shape => isWfShapeExactHOL context shape) then
              let info : StructInfoHOLExact :=
                { fields := fields, size := sizeOfShapeWithContextHOL context (.comb shapes) }
              decsStcnamesHOLExact (width := width) ((struct, info) :: context) rest
            else none
          else none
  | .decl _ _ _ :: rest => decsStcnamesHOLExact (width := width) context rest
  | .function _ :: rest => decsStcnamesHOLExact (width := width) context rest
  | .exnDecl _ _ :: rest => decsStcnamesHOLExact (width := width) context rest

@[simp] theorem decsStcnamesHOLExact_nil {width : Nat} [NeZero width]
    (context : StructContextExact) :
    decsStcnamesHOLExact (width := width) context [] = some context := rfl

end Flapjack