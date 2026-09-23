import Flapjack.HolRef
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.PanToCrep.Compile

/-!
HOL-shaped top-level Pancake-to-Crep compiler boundary. The compilation
produces HOL's function triples and passes those directly to the exact
`compile_inl_top` counterpart; metadata is attached only in a downstream
adapter for Flapjack's existing pipeline representation.
-/

namespace Flapjack

/-- Exact port of Cake `pan_to_crep$compile_prog`
    (`cakeml/pancake/pan_to_crepScript.sml:393`). It compiles declarations to
    the HOL triple list, selects inline names using `functions (FILTER
    inlinable declarations)`, and applies the exact triple-list
    `compileInlTopHOL` pass. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_prog_def"]
def compileProgTopHOL [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width))) :
    List (FunName × List Nat × CrepProg (BitVec width)) :=
  let inlineNames :=
    (functionEntries (declarations.filter inlinable)).map
      fun (name, _, _, _) => name
  compileInlTopHOL inlineNames (compileToCrepHOL declarations)

/-! Metadata adapter following the exact `compile_prog` triple boundary.
The Cake passes following `compile_prog` consume triples; the production
Flapjack pipeline keeps the source return shape in `CompiledFunction`. -/
def compileProgTopHOLWithMetadata [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width))) :
    List (CompiledFunction (BitVec width)) :=
  (compileToCrepHOLWithMetadata declarations).zipWith
    (fun original (_, _, body) => { original with body })
    (compileProgTopHOL declarations)

end Flapjack
