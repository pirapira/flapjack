import Flapjack.PanStructs

namespace Flapjack.Test.PanStructsCompileExpParity

/-! Direct parity for `pan_structs$compile_exp_def`
    (`pan_structsScript.sml:107`). The cases mirror the direct HOL fixture. -/
def context : StructPassContext :=
  { structs := [ ("Pair", { fields := [("left", .one),
      ("right", .comb [.one, .one])], size := 3 }) ]
    locals := [("local", .comb [.one, .one])]
    globals := [("global", .named "Pair")] }

def parityGuard : Bool :=
  (match structCompileExp context
      (.rStruct [.const 1, .const 2] : Exp Nat) with
  | .rStruct [.const 1, .const 2] => true
  | _ => false) &&
  (match structCompileExp context
      (.rField 1 (.rStruct [.const 1, .const 2]) : Exp Nat) with
  | .rField 1 (.rStruct [.const 1, .const 2]) => true
  | _ => false) &&
  (match structCompileExp context
      (.nStruct "Pair" [("right", .const 2), ("left", .const 1)] : Exp Nat) with
  | .rStruct [.const 1, .const 2] => true
  | _ => false) &&
  (match structCompileExp context
      (.nField "right" (.nStruct "Pair" []) : Exp Nat) with
  | .rField 1 (.rStruct []) => true
  | _ => false) &&
  (match structCompileExp context
      (.load (.named "Pair") (.const 0) : Exp Nat) with
  | .load (.comb [.one, .comb [.one, .one]]) (.const 0) => true
  | _ => false) &&
  (match structCompileExp context
      (.load32 (.const 0) : Exp Nat) with
  | .load32 (.const 0) => true
  | _ => false) &&
  (match structCompileExp context
      (.loadByte (.const 0) : Exp Nat) with
  | .loadByte (.const 0) => true
  | _ => false) &&
  (match structCompileExp context (.const 0 : Exp Nat) with
  | .const 0 => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanStructsCompileExpParity
