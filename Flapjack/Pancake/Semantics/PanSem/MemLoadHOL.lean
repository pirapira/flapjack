import Flapjack.HolRef
import Flapjack.Pancake.PanLang.Shape
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.Semantics.PanSem.ValueHOL

/-!
# Exact `panSem$mem_load` over the faithful `mlstring` carriers

HOL `mem_load` (`cakeml/pancake/semantics/panSemScript.sml:137-166`) reads a
value of a given shape from a total word memory guarded by a domain, using the
structure context `stcs : (stcname # 'a struct_info) list` to resolve `Named`
shapes and to advance the address by `size_of_sh_with_ctxt stcs shape`.

```
mem_load One addr dm m stcs =
  if addr IN dm then SOME (Val (m addr)) else NONE
mem_load (Comb shapes) addr dm m stcs =
  case mem_loads shapes addr dm m stcs of SOME vs => SOME (RStruct vs) | NONE => NONE
mem_load (Named nm) addr dm m stcs =
  case dropWhile (λ(n,i). ~(n = nm)) stcs of
    (nm,info)::stcs' =>
      (case mem_load_flds info.fields addr dm m stcs' of
         SOME vflds => SOME (NStruct nm vflds) | NONE => NONE)
  | _ => NONE
```

This module gives the exact port over the exact carriers `ShapeHOL`,
`StructContextExact` (`= List (MlStringHOL × StructInfoHOLExact)`),
`ValueHOL width` and the faithful `HolWordLab width`.  It mirrors the untagged
HOL-shaped implementation `panMemLoadHOL` in
`Flapjack/Pancake/Semantics/PanSemStateEval.lean`, which instead uses the
production `Shape`/`StructContextHOL`/`HolValue` carriers whose names are Lean
`String`.  Because this port uses the exact `mlstring`-keyed carriers throughout,
its `@[hol ... "mem_load_def"]` tag is justified; the untagged production
counterpart stays where it is so the executable stack is untouched.
-/

namespace Flapjack

/-- The faithful Cake `mlstring` carrier, local abbreviation. -/
abbrev MlStringHOLM := Flapjack.Basis.Pure.MlString.MlString

/-- Exact structure context: HOL `(stcname # 'a struct_info) list`. -/
abbrev StructContextHOLM := List (MlStringHOLM × Flapjack.Pancake.PanLang.StructInfoHOLExact)

/-- HOL `bytes_in_word = n2w (dimindex (:'a) DIV 8)`. -/
def bytesInWordHOL (width : Nat) : BitVec width := BitVec.ofNat width (width / 8)

mutual
  /-- Exact port of HOL `mem_load` (`cakeml/pancake/semantics/panSemScript.sml:137`). -/
  @[hol "cakeml/pancake/semantics/panSemScript.sml" "mem_load_def"]
  def memLoadHOLExact {width : Nat} [NeZero width] (shape : Flapjack.Pancake.PanLang.ShapeHOL)
      (address : BitVec width) (domain : BitVec width → Prop) [DecidablePred domain]
      (memory : BitVec width → HolWordLab width) (context : StructContextHOLM) :
      Option (ValueHOL width) :=
    match shape with
    | .one => if domain address then some (.val (memory address)) else none
    | .comb shapes =>
        match memLoadsHOLExact shapes address domain memory context with
        | some values => some (.rStruct values)
        | none => none
    | .named name =>
        match context with
        | [] => none
        | (candidate, info) :: rest =>
            if candidate = name then
              match memLoadFldsHOLExact info.fields address domain memory rest with
              | some fields => some (.nStruct candidate fields)
              | none => none
            else memLoadHOLExact (.named name) address domain memory rest
  termination_by (context.length, sizeOf shape)
  decreasing_by
    all_goals
      simp_wf
      first
      | omega
      | (rename_i hmem
         have := List.sizeOf_lt_of_mem hmem
         omega)

  /-- Exact port of HOL `mem_loads` (`cakeml/pancake/semantics/panSemScript.sml:153`). -/
  def memLoadsHOLExact {width : Nat} [NeZero width] (shapes : List Flapjack.Pancake.PanLang.ShapeHOL)
      (address : BitVec width) (domain : BitVec width → Prop) [DecidablePred domain]
      (memory : BitVec width → HolWordLab width) (context : StructContextHOLM) :
      Option (List (ValueHOL width)) :=
    match shapes with
    | [] => some []
    | shape :: rest =>
        match memLoadHOLExact shape address domain memory context,
              memLoadsHOLExact rest
                (address + bytesInWordHOL width *
                  BitVec.ofNat width (Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context shape))
                domain memory context with
        | some value, some values => some (value :: values)
        | _, _ => none
  termination_by (context.length, sizeOf shapes)
  decreasing_by
    all_goals
      simp_wf
      first
      | omega
      | (rename_i hmem
         have := List.sizeOf_lt_of_mem hmem
         omega)

  /-- Exact port of HOL `mem_load_flds` (`cakeml/pancake/semantics/panSemScript.sml:161`). -/
  def memLoadFldsHOLExact {width : Nat} [NeZero width]
      (fields : List (MlStringHOLM × Flapjack.Pancake.PanLang.ShapeHOL))
      (address : BitVec width) (domain : BitVec width → Prop) [DecidablePred domain]
      (memory : BitVec width → HolWordLab width) (context : StructContextHOLM) :
      Option (List (MlStringHOLM × ValueHOL width)) :=
    match fields with
    | [] => some []
    | (field, shape) :: rest =>
        match memLoadHOLExact shape address domain memory context,
              memLoadFldsHOLExact rest
                (address + bytesInWordHOL width *
                  BitVec.ofNat width (Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context shape))
                domain memory context with
        | some value, some values => some ((field, value) :: values)
        | _, _ => none
  termination_by (context.length, sizeOf fields)
  decreasing_by
    all_goals
      simp_wf
      first
      | omega
      | (rename_i hpair
         have : sizeOf shape < sizeOf ((field, shape) : MlStringHOLM × Flapjack.Pancake.PanLang.ShapeHOL) := by
           simp +arith
         have := List.sizeOf_lt_of_mem hpair
         omega)
      | (rename_i hmem
         have := List.sizeOf_lt_of_mem hmem
         omega)
end

end Flapjack