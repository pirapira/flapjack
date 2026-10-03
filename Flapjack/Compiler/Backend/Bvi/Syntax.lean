import Flapjack.Compiler.Backend.ClosLang.Syntax

namespace Flapjack.Compiler.Backend.Bvi

/-- Complete original expression syntax; the operation payload is the actual
ClosLang.Op carrier. Every recursive List/Option and numeric payload is retained. -/
@[hol "cakeml/compiler/backend/bviScript.sml" "exp"]
inductive Exp where
  | var : Nat → Exp
  | ifThenElse : Exp → Exp → Exp → Exp
  | «let» : List Exp → Exp → Exp
  | raise : Exp → Exp
  | tick : Exp → Exp
  | call : Nat → Option Nat → List Exp → Option Exp → Exp
  | force : Nat → Nat → Exp
  | op : ClosLang.Op → List Exp → Exp
  | letCall : Nat → Nat → Nat → List Exp → Exp → Exp
  | «return» : List Exp → Exp

end Flapjack.Compiler.Backend.Bvi
