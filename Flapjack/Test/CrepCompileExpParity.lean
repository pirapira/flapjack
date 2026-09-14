import Flapjack.CrepToLoop

/-! Direct parity for `crep_to_loop$compile_exp_def` at
`cakeml/pancake/crep_to_loopScript.sml:50`.  The three-argument Mul case keeps
the source pass's destination at `tmp + LENGTH es`; the live set is compared
as membership because Lean stores it as a list while HOL uses `num_set`. -/
namespace Flapjack.Test.CrepCompileExpParity

def context : LoopContext Nat :=
  { vars := [], functions := [], maxVar := 0, target := .rv64i }

def compiled :=
  loopCompileExp context 10 []
    (.crepOp .mul [.const 2, .const 3, .const 4])

def parityGuard : Bool :=
  match compiled with
  | { code :=
        [.assign 10 (.const 2), .assign 11 (.const 3),
         .assign 12 (.const 4), .arith (.longMul 13 13 10 11)],
      expression := .var 13, nextTemp := 14, live := live } =>
      live.length == 4 &&
        live.contains 10 && live.contains 11 &&
        live.contains 12 && live.contains 13
  | _ => false

#eval compiled
#guard parityGuard

end Flapjack.Test.CrepCompileExpParity
