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

/- Direct parity for `pan_structs$compile_def` (`pan_structsScript.sml:157`).
   The declaration-local context is observable here: the body field lookup
   must use the source shape bound by `Dec`, while the emitted declaration
   carries the recursively compiled shape. -/
def compileProgParityGuard : Bool :=
  match structCompileProg context
      (.dec "value" (.named "Pair")
        (.nStruct "Pair" [("left", .const 1), ("right", .const 2)])
        (.return (.nField "right" (.var .local "value"))) : Prog Nat) with
  | .dec "value" (.comb [.one, .comb [.one, .one]])
      (.rStruct [.const 1, .const 2])
      (.return (.rField 1 (.var .local "value"))) => true
  | _ => false

#eval compileProgParityGuard
#guard compileProgParityGuard

end Flapjack.Test.PanStructsCompileExpParity
