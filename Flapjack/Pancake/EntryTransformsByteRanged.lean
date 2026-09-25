import Flapjack.Pipeline
import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.PanLang.Decl

/-!
Byte-rangedness of the first two executed entry transforms
(bead `flapjack-pxn.18.3.5.8.7.1.3`).

`Flapjack.Pipeline.compileFlapjackEntryCake` runs, in order,

1. `panTargetMoveStartToFront start declarations` (the source-order entry
   relocation of Cake's `pan_to_target_all`, `pan_passesScript.sml:20-37`),
2. `panSimpDecls` (Cake's `pan_simp`),
3. `structCompileTop`, `globalCompileTopCake`, ...

before the result reaches `compileProgTopHOLWithMetadata`.  The raw
`parseTopDecs` bridge `parseTopDecs_declByteRanged` only covers the parser
output; the post-pass list must still be shown byte-ranged.  This module
discharges the first two transforms:

* `panTargetMoveStartToFront_byteRanged`: the relocation is a pair of
  `globalDeclsFilter`s, so it only permutes the input and preserves the
  predicate;
* `panSimpDecls_byteRanged` (in `Flapjack.Pancake.PanSimp`): `pan_simp` only
  rewrites function bodies via `panSimpProg`, which preserves `ProgByteRanged`;
* `entryFirstTwoTransforms_byteRanged`: the composed statement.

Nothing here is a HOL-tagged declaration: these are Flapjack-only preservation
lemmas about the executable transforms, so no manifest or type-lock entry is
needed.  The remaining passes (`structCompileTop`, `globalCompileTopCake`,
`globalRenameDecls`, `globalResortDecls`) are tracked by the parent bead.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- A declaration produced by `globalDeclsFilter` comes from the input list.
    The existing `mem_globalDeclsFilter` only records that the predicate held,
    which is enough here because `DeclByteRanged` is embedded by the caller. -/
theorem mem_of_mem_globalDeclsFilter {α : Type} {predicate : Decl α → Bool}
    {declaration : Decl α} {declarations : List (Decl α)}
    (hmem : declaration ∈ globalDeclsFilter predicate declarations) :
    declaration ∈ declarations := by
  induction declarations with
  | nil => rw [globalDeclsFilter.eq_def] at hmem; simp at hmem
  | cons head tail ih =>
      simp only [globalDeclsFilter] at hmem
      by_cases hpred : predicate head = true
      · simp [hpred] at hmem
        rcases hmem with heq | htail
        · subst heq; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem head (ih htail)
      · simp [hpred] at hmem
        exact List.mem_cons_of_mem head (ih hmem)

/-- Entry relocation (`panTargetMoveStartToFront`) keeps every declaration
    byte-ranged.  The transform is `filter (name = start) ++ filter (name ≠
    start)`, so the result is a sublist of the input and the predicate is
    inherited. -/
theorem panTargetMoveStartToFront_byteRanged {width : Nat} [BEq String]
    (start : FunName) (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ d ∈ panTargetMoveStartToFront start declarations, DeclByteRanged d := by
  intro d hd
  unfold panTargetMoveStartToFront at hd
  rw [List.mem_append] at hd
  rcases hd with hd | hd
  · exact h d (mem_of_mem_globalDeclsFilter hd)
  · exact h d (mem_of_mem_globalDeclsFilter hd)

/-- The list after the first two executed entry transforms
    (`panTargetMoveStartToFront` then `panSimpDecls`) is byte-ranged whenever
    the parser output is.  This is the post-pass list
    `compileFlapjackEntryCake` builds before `structCompileTop`. -/
theorem entryFirstTwoTransforms_byteRanged {width : Nat} [BEq String]
    (start : FunName) (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ d ∈ panSimpDecls (panTargetMoveStartToFront start declarations),
      DeclByteRanged d :=
  panSimpDecls_byteRanged _
    (panTargetMoveStartToFront_byteRanged start declarations h)

end Flapjack
