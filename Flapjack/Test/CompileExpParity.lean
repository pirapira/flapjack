import Flapjack.PanToCrep

/-!
# Original-domain parity for `pan_to_crep$compile_exp`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/compile_exp_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:39-101`.
-/

namespace Flapjack.Test.CompileExpParity

open Flapjack

def context : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 8 }

def oneResultOK (expected : List (CrepExp Nat)) :
    List (CrepExp Nat) × Shape → Bool
  | (actual, .one) => actual == expected
  | _ => false

def combTwoResultOK (expected : List (CrepExp Nat)) :
    List (CrepExp Nat) × Shape → Bool
  | (actual, .comb [.one, .one]) => actual == expected
  | _ => false

def leavesOK : Bool :=
  oneResultOK [.const 7] (compileExp context (.const 7)) &&
  oneResultOK [.const 0] (compileExp context (.var .global "g")) &&
  oneResultOK [.baseAddr] (compileExp context (.baseAddr)) &&
  oneResultOK [.topAddr] (compileExp context (.topAddr))

def structFieldOK : Bool :=
  combTwoResultOK [.const 1, .const 2]
      (compileExp context (.rStruct [.const 1, .const 2])) &&
  oneResultOK [.const 2]
      (compileExp context (.rField 1 (.rStruct [.const 1, .const 2])))

def loadsOpsOK : Bool :=
  oneResultOK [.load32 (.const 3)]
      (compileExp context (.load32 (.const 3))) &&
  oneResultOK [.loadByte (.const 4)]
      (compileExp context (.loadByte (.const 4))) &&
  oneResultOK [.op .add [.const 1, .const 2]]
      (compileExp context (.op .add [.const 1, .const 2])) &&
  oneResultOK [.crepOp .mul [.const 5, .const 6]]
      (compileExp context (.panOp .mul [.const 5, .const 6]))

def cmpShiftOK : Bool :=
  oneResultOK [.cmp .equal (.const 1) (.const 0)]
      (compileExp context (.cmp .equal (.const 1) (.const 0))) &&
  oneResultOK [.shift .lsl (.const 2) (.const 1)]
      (compileExp context (.shift .lsl (.const 2) (.const 1)))

def parityGuard : Bool := leavesOK && structFieldOK && loadsOpsOK && cmpShiftOK

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS compile_exp leaves/struct-field/loads/ops/cmp-shift"
  else
    IO.println "FAIL compile_exp parity"
  pure parityGuard

end Flapjack.Test.CompileExpParity
