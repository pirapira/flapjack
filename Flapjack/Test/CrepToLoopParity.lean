import Flapjack.CrepToLoop

/-!
Direct parity for `crep_to_loop$compile` (`crep_to_loopScript.sml:120`).
The checked-in HOL fixture covers `Skip` and `Raise`; the latter observes the
compiler-generated temporary assignment before the terminal raise.
-/
namespace Flapjack.Test.CrepToLoopParity

def compileContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [], maxVar := 0, target := .rv64i }

def originalCompileSkip : LoopProg Nat := .skip

def originalCompileRaise : LoopProg Nat :=
  .seq (.assign 1 (.const 17)) (.raise 1)

def leanCompileSkip : LoopProg Nat :=
  compileCrepToLoop compileContext [] (.skip : CrepProg Nat)

def leanCompileRaise : LoopProg Nat :=
  compileCrepToLoop compileContext [] (.raise 17 : CrepProg Nat)

#eval leanCompileSkip
#eval leanCompileRaise

def parityGuard : Bool :=
  match leanCompileSkip, originalCompileSkip, leanCompileRaise, originalCompileRaise with
  | .skip, .skip,
    .seq (.assign 1 (.const 17)) (.raise 1),
    .seq (.assign 1 (.const 17)) (.raise 1) => true
  | _, _, _, _ => false

#eval parityGuard
#guard parityGuard

end Flapjack.Test.CrepToLoopParity
