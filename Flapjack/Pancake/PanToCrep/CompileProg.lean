import Flapjack.HolRef
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanLang.Decl

/-!
HOL-shaped top-level Pancake-to-Crep compiler boundary. The compilation
produces HOL's function triples and passes those directly to the exact
`compile_inl_top` counterpart; metadata is attached only in a downstream
adapter for Flapjack's existing pipeline representation.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's
    `pan_to_crep$compile_prog`
    (`cakeml/pancake/pan_to_crepScript.sml:393`). It compiles declarations to
    the HOL triple list, selects inline names using `functions (FILTER
    inlinable declarations)`, and applies the exact triple-list
    `compileInlTopHOL` pass. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the declarations and inline
-- names are keyed by `FunName` = `String`, while HOL `pan_to_crepScript.sml`
-- keys `compile_prog`/`functions` by `funname` = `mlstring` (tracked by
-- `flapjack-pxn.18.3.5.8`, parent `flapjack-pxn.18.3.5.7.2`).
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

/-! Exact-carrier interface for the `compile_prog` boundary (bead
    flapjack-pxn.18.3.5.8.6). It consumes the MLString-keyed declaration
    carrier `DeclHOL` and converts byte-ranged names at the boundary via
    `declOfHOL`, so the exact HOL carriers are the interface type of the
    declaration-level compiler boundary. The executed source path still builds
    production `Decl` from `Parser.parseTopDecs`; see the nonbyte blocker
    recorded in `Flapjack/Test/PanLangDeclHOLParity.lean`. -/
def compileProgTopHOLOfExact {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (DeclHOL width)) :
    List (FunName × List Nat × CrepProg (BitVec width)) :=
  compileProgTopHOL (declarations.map declOfHOL)

/-- Byte-ranged production declarations round-trip through the exact carrier. -/
theorem map_declOfHOL_declToHOL {width : Nat} [NeZero width]
    (declarations : List (Flapjack.Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    (declarations.map declToHOL).map declOfHOL = declarations := by
  induction declarations with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons]
      rw [declOfHOL_declToHOL d (h d (by simp)),
        ih (fun e he => h e (by simp [he]))]

/-- The exact-carrier `compile_prog` boundary agrees with the production
    compiler on every byte-ranged declaration list. -/
theorem compileProgTopHOLOfExact_declToHOL {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Flapjack.Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    compileProgTopHOLOfExact (declarations.map declToHOL) =
      compileProgTopHOL declarations := by
  unfold compileProgTopHOLOfExact
  rw [map_declOfHOL_declToHOL declarations h]

end Flapjack
