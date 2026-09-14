import Flapjack.Language

/-! Parity guard for `panLang$inlinable` from
    `cakeml/pancake/panLangScript.sml:389-391`. -/

namespace Flapjack.Test.PanLangInlinableParity

open Flapjack

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

end Flapjack.Test.PanLangInlinableParity
