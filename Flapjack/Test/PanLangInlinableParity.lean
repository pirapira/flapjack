import Flapjack.Pancake.PanLang
import Flapjack.Pancake.PanLang.Decl

/-! Parity guard for `panLang$inlinable` from
    `cakeml/pancake/panLangScript.sml:389-391`. -/

namespace Flapjack.Test.PanLangInlinableParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def functionDecl (flag : Bool) : Decl Nat :=
  .function
    { name := "f"
      inline := flag
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def parityGuard : Bool :=
  inlinable (functionDecl true) == true &&
  inlinable (functionDecl false) == false &&
  inlinable (.decl .one "x" (.const 0)) == false

#guard parityGuard
#eval parityGuard

/-! ## Exact-carrier `inlinable` parity (bead flapjack-4ac.1.47) -/

def functionDeclHOL (flag : Bool) : DeclHOL 8 :=
  .function
    { name := ofString "f"
      inline := flag
      exported := false
      params := []
      body := .skip
      returnShape := ShapeHOL.one }

def parityGuardHOL : Bool :=
  inlinableHOL (functionDeclHOL true) == true &&
  inlinableHOL (functionDeclHOL false) == false &&
  inlinableHOL (.decl ShapeHOL.one (ofString "x") (.const 0) : DeclHOL 8) == false

#guard parityGuardHOL

example : inlinableHOL (functionDeclHOL true) = true := rfl
example : inlinableHOL (functionDeclHOL false) = false := rfl
example : inlinableHOL (.decl ShapeHOL.one (ofString "x") (.const 0) : DeclHOL 8) = false :=
  rfl
example : Flapjack.inlinable (declOfHOL (functionDeclHOL true)) =
    inlinableHOL (functionDeclHOL true) :=
  inlinable_declOfHOL _

def productionUnicodeInline : Flapjack.Decl (BitVec 8) :=
  .function
    { name := String.singleton (Char.ofNat 0x1d518)
      inline := true
      exported := false
      params := []
      body := .skip
      returnShape := .one }

def exactFilterPreservesUnicodeName : Bool :=
  match ([productionUnicodeInline].filter inlinableThroughHOL) with
  | [.function declaration] =>
      declaration.name == String.singleton (Char.ofNat 0x1d518) && declaration.inline
  | _ => false

#guard exactFilterPreservesUnicodeName

example {width : Nat} [NeZero width]
    (declarations : List (Flapjack.Decl (BitVec width))) :
    declarations.filter inlinableThroughHOL =
      declarations.filter Flapjack.inlinable :=
  filter_inlinableThroughHOL declarations

end Flapjack.Test.PanLangInlinableParity
