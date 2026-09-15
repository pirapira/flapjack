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

/-- Context used for the call-lowering characterization. Function `1` maps to
    loop label `3`, so the generated call targets `some 3`. -/
def callContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [("f", (3, 1))], maxVar := 4, target := .rv64i }

/-- `crep_to_loop$compile` on `call (SOME ([9], NONE)) 1 [Const 3]`.

    The original always emits a default handler `rt2` for a call returning
    through an exception channel (`crep_to_loopScript.sml:193-206`); for
    `handler = NONE` that `rt2` binds the caught exception and immediately
    re-raises it, which is observationally indistinguishable from an absent
    source handler. -/
def leanCompileCallNoHandler : LoopProg Nat :=
  compileCrepToLoop callContext [] (.call (some ([9], none)) "f" [.const 3])

/-- `crep_to_loop$compile` on a call that names an exception handler, which
    must carry an `rt2` handler exactly like the original. -/
def leanCompileCallWithHandler : LoopProg Nat :=
  compileCrepToLoop callContext []
    (.call (some ([9], some (7, .skip))) "f" [.const 3])

/-- A handler-less source call still carries Cake's default raise handler. -/
def handlerlessCallCarriesRaiseHandler : Bool :=
  match leanCompileCallNoHandler with
  | .seq _ (.call _ (some 3) _ (some (5, .raise 5, .skip, []))) => true
  | _ => false

/-- A call that names an exception handler does emit an `rt2`. -/
def handledCallCarriesRaiseHandler : Bool :=
  match leanCompileCallWithHandler with
  | .seq _ (.call _ (some 3) _ (some _)) => true
  | _ => false

#eval leanCompileCallNoHandler
#eval leanCompileCallWithHandler

#guard handlerlessCallCarriesRaiseHandler
#guard handledCallCarriesRaiseHandler

end Flapjack.Test.CrepToLoopParity
