import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanLang.Prog

/-!
Byte-range preservation facts for the executed PanGlobals pass.

The exact DeclHOL compiler boundary can only be used after the production
String declarations have been shown to round-trip through DeclHOL. The parser
provides that invariant, but the final global pass also rewrites programs and
can synthesize names. These lemmas establish the pass-local facts needed to
prove the invariant at the actual compiler boundary.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

private theorem nameRanged_append {left right : String}
    (hleft : NameRanged left) (hright : NameRanged right) :
    NameRanged (left ++ right) := by
  intro character hcharacter
  rw [String.toList_append, List.mem_append] at hcharacter
  rcases hcharacter with h | h
  · exact hleft character h
  · exact hright character h

private theorem globalApostrophes_nameRanged (count : Nat) :
    NameRanged (globalApostrophes count) := by
  induction count with
  | zero => simp [globalApostrophes, NameRanged]
  | succ count ih =>
      apply nameRanged_append
      · decide
      · simpa [globalApostrophes] using ih

private theorem freshNameHOL_literal_byteRanged (seed : String)
    (hseed : NameRanged seed) (names : List String) :
    NameRanged (freshNameHOL seed names) :=
  holMlStringWitness_freshNameHOL seed names hseed

/-- Every shape found in a global compilation context is byte-ranged. -/
def GlobalContextShapesByteRanged [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) : Prop :=
  ∀ name shape address,
    lookupInfo name context.globals = some (shape, address) → ShapeByteRanged shape

/-- Byte-ranged shapes compile to byte-ranged shape-value expressions. -/
theorem globalShapeVal_byteRanged {width : Nat}
    (context : GlobalPassContext (BitVec width)) :
    ∀ shape, ShapeByteRanged shape →
      ExpByteRanged (globalShapeVal context shape) := by
  apply Flapjack.Shape.rec
    (motive_1 := fun shape => ShapeByteRanged shape →
      ExpByteRanged (globalShapeVal context shape))
    (motive_2 := fun shapes =>
      (∀ shape ∈ shapes, ShapeByteRanged shape) →
        ListExpByteRanged (shapes.map (globalShapeVal context)))
  · intro _
    simp [globalShapeVal, ExpByteRanged]
  · intro shapes ih
    intro hshape
    simp only [ShapeByteRanged] at hshape
    simpa [globalShapeVal, ExpByteRanged] using ih hshape
  · intro _ _
    simp [globalShapeVal, ExpByteRanged]
  · intro _
    simp [ListExpByteRanged]
  · intro head tail ihHead ihTail hshapes
    simp only [ListExpByteRanged, List.map_cons]
    exact ⟨ihHead (hshapes head (by simp)), ihTail (by
      intro shape hshape
      exact hshapes shape (by simp [hshape]))⟩

theorem globalCompileExp_byteRanged [BEq String]
    {width : Nat} (context : GlobalPassContext (BitVec width))
    (hcontext : GlobalContextShapesByteRanged context) :
    ∀ expression : Exp (BitVec width), ExpByteRanged expression →
      ExpByteRanged (globalCompileExp context expression) := by
  apply globalCompileExp.induct context
    (motive1 := fun expressions =>
      ListExpByteRanged expressions →
        ListExpByteRanged (globalCompileExp.globalCompileExps context expressions))
    (motive2 := fun expression =>
      ExpByteRanged expression → ExpByteRanged (globalCompileExp context expression))
  case case4 =>
    intro name shape address hlookup _hname
    simpa [globalCompileExp, hlookup, ExpByteRanged, ListExpByteRanged] using
      hcontext name shape address hlookup
  all_goals
    try simp_all [globalCompileExp, globalCompileExp.globalCompileExps,
      ExpByteRanged, ListExpByteRanged]

private theorem globalCompileExpList_byteRanged [BEq String]
    {width : Nat} (context : GlobalPassContext (BitVec width))
    (hcontext : GlobalContextShapesByteRanged context) :
    ∀ expressions : List (Exp (BitVec width)), ListExpByteRanged expressions →
      ∀ expression ∈ globalCompileExpList context expressions,
        ExpByteRanged expression := by
  intro expressions
  induction expressions with
  | nil => intro _ expression hmem; simp [globalCompileExpList] at hmem
  | cons head rest ih =>
      intro hinput expression hmem
      simp only [ListExpByteRanged] at hinput
      simp only [globalCompileExpList, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · cases heq
        exact globalCompileExp_byteRanged context hcontext head hinput.1
      · exact ih hinput.2 expression hmem

end Flapjack
