import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect
import Flapjack.Pancake.PanLang.Decl

/-! Regression for the exact-carrier port of
`pan_structsProofScript.sml:size_of_sh_with_ctxt_drop`, paired with the direct
HOL EVAL rows in `scripts/hol-probes/pan_structs_shape_context_drop_probe.out`.
The nonempty context prefix and suffix both carry distinct MlString names. -/

namespace Flapjack.Test

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

private def shapeContextDropContext : StructContextExact :=
  [(ofString "Prefix", { fields := [], size := 1 }),
   (ofString "Target", { fields := [], size := 3 })]

private def shapeContextDropNamed : ShapeHOL :=
  .named (ofString "Target")

private def shapeContextDropNested : ShapeHOL :=
  .comb [.one, shapeContextDropNamed, .comb [shapeContextDropNamed, .one]]

example :
    sizeOfShapeWithContextHOL (shapeContextDropContext.drop 1) .one =
      sizeOfShapeWithContextHOL shapeContextDropContext .one := by
  exact sizeOfShapeWithContextHOL_drop shapeContextDropContext .one 1 rfl (by decide)

example :
    sizeOfShapeWithContextHOL (shapeContextDropContext.drop 1) shapeContextDropNamed =
      sizeOfShapeWithContextHOL shapeContextDropContext shapeContextDropNamed := by
  apply sizeOfShapeWithContextHOL_drop shapeContextDropContext shapeContextDropNamed 1
  · decide
  · decide

example :
    sizeOfShapeWithContextHOL (shapeContextDropContext.drop 1) shapeContextDropNested =
      sizeOfShapeWithContextHOL shapeContextDropContext shapeContextDropNested := by
  apply sizeOfShapeWithContextHOL_drop shapeContextDropContext shapeContextDropNested 1
  · decide
  · decide

private def shapeContextDropRows : Bool :=
  isWfShapeExactHOL (shapeContextDropContext.drop 1) .one &&
  decide ((shapeContextDropContext.map Prod.fst).Nodup) &&
  decide (sizeOfShapeWithContextHOL (shapeContextDropContext.drop 1) .one =
    sizeOfShapeWithContextHOL shapeContextDropContext .one) &&
  isWfShapeExactHOL (shapeContextDropContext.drop 1) shapeContextDropNamed &&
  isWfShapeExactHOL (shapeContextDropContext.drop 1) shapeContextDropNested &&
  decide (sizeOfShapeWithContextHOL (shapeContextDropContext.drop 1) shapeContextDropNamed =
    sizeOfShapeWithContextHOL shapeContextDropContext shapeContextDropNamed) &&
  decide (sizeOfShapeWithContextHOL (shapeContextDropContext.drop 1) shapeContextDropNested =
    sizeOfShapeWithContextHOL shapeContextDropContext shapeContextDropNested)

#eval if shapeContextDropRows then
  IO.println "PASS pan_structs size_of_sh_with_ctxt_drop exact-carrier rows (One, Named, nested Comb)"
else
  throw (IO.userError "FAIL pan_structs size_of_sh_with_ctxt_drop exact-carrier rows")

end Flapjack.Test
