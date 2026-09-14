import Flapjack.CrepToLoop

/-! Direct parity for `crep_to_loop$compile_crepop` at line 42. -/
namespace Flapjack.Test.CompileCrepOpParity

def originalCompileCrepOp : List (LoopProg Nat) × Nat :=
  ([.arith (.longMul 4 4 2 3)], 4)

def leanCompileCrepOp : List (LoopProg Nat) × Nat :=
  compileCrepOp .mul .rv64i 2 3 4 []

def parityGuard : Bool :=
  match leanCompileCrepOp with
  | ([.arith (.longMul 4 4 2 3)], 4) => true
  | _ => false

#guard parityGuard

end Flapjack.Test.CompileCrepOpParity
