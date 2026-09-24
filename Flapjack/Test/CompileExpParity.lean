import Flapjack.Pancake.PanToCrep.Compile

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

def finiteMapContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE (FUPDATE FEMPTY ("p", (.one, [3]))) ("p", (.one, [5]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 5 }

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

/-! The value and duplicate-key case are checked against the direct HOL probe
    `finite_map_shadow` in `compile_exp_probe.out`. This exercises HOL's
    `FUPDATE` lookup semantics through the native finite-map context. -/
def finiteMapLookupOK : Bool :=
  match compileExpHOL finiteMapContext (.var .local "p") with
  | ([.var 5], .one) => true
  | _ => false

/-! This mirrors the direct HOL `finite_map_load32_local` observation and
    checks the one-word Local Load32 compilation shape used by Call arguments. -/
def finiteMapLoad32LocalOK : Bool :=
  match compileExpHOL finiteMapContext (.load32 (.var .local "p")) with
  | ([.load32 (.var 5)], .one) => true
  | _ => false

/-! The remaining probe rows are reproduced through the tagged finite-map
    `compileExpHOL`. These mirror the `compileExp` rows above but exercise the
    HOL-shaped path used by `compileProgHOL`/`compileProgRiscV`. -/
def holLeavesOK : Bool :=
  oneResultOK [.const 7] (compileExpHOL finiteMapContext (.const 7)) &&
  oneResultOK [.const 0] (compileExpHOL finiteMapContext (.var .global "g")) &&
  oneResultOK [.baseAddr] (compileExpHOL finiteMapContext (.baseAddr)) &&
  oneResultOK [.topAddr] (compileExpHOL finiteMapContext (.topAddr))

def holStructFieldOK : Bool :=
  combTwoResultOK [.const 1, .const 2]
      (compileExpHOL finiteMapContext (.rStruct [.const 1, .const 2])) &&
  oneResultOK [.const 2]
      (compileExpHOL finiteMapContext (.rField 1 (.rStruct [.const 1, .const 2])))

def holLoadsOpsOK : Bool :=
  oneResultOK [.load32 (.const 3)]
      (compileExpHOL finiteMapContext (.load32 (.const 3))) &&
  oneResultOK [.loadByte (.const 4)]
      (compileExpHOL finiteMapContext (.loadByte (.const 4))) &&
  oneResultOK [.op .add [.const 1, .const 2]]
      (compileExpHOL finiteMapContext (.op .add [.const 1, .const 2])) &&
  oneResultOK [.crepOp .mul [.const 5, .const 6]]
      (compileExpHOL finiteMapContext (.panOp .mul [.const 5, .const 6]))

def holCmpShiftOK : Bool :=
  oneResultOK [.cmp .equal (.const 1) (.const 0)]
      (compileExpHOL finiteMapContext (.cmp .equal (.const 1) (.const 0))) &&
  oneResultOK [.shift .lsl (.const 2) (.const 1)]
      (compileExpHOL finiteMapContext (.shift .lsl (.const 2) (.const 1)))

def parityGuard : Bool :=
  leavesOK && structFieldOK && loadsOpsOK && cmpShiftOK && finiteMapLookupOK &&
  finiteMapLoad32LocalOK &&
  holLeavesOK && holStructFieldOK && holLoadsOpsOK && holCmpShiftOK

example : compileExpHOL finiteMapContext (.load32 (.var .local "p")) =
    ([.load32 (.var 5)], .one) := by
  simp [compileExpHOL, finiteMapContext, FLOOKUP, FUPDATE]

example : compileExpHOL finiteMapContext (.var .local "p") = ([.var 5], .one) := by
  simp [compileExpHOL, finiteMapContext, FLOOKUP, FUPDATE]

example : compileExpHOL finiteMapContext (.rField 1 (.rStruct [.const 1, .const 2])) =
    ([.const 2], .one) := by
  simp [compileExpHOL, compileExpHOL.compileExpListHOL, compileField,
    finiteMapContext]

example : compileExpHOL finiteMapContext (.panOp .mul [.const 5, .const 6]) =
    ([.crepOp .mul [.const 5, .const 6]], .one) := by
  simp [compileExpHOL, compileExpHOL.compileExpListHOL, cexpHeads,
    compilePanOp, finiteMapContext]

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS compile_exp leaves/struct-field/loads/ops/cmp-shift/finite-map (tagged compileExpHOL)"
  else
    IO.println "FAIL compile_exp parity"
  pure parityGuard

end Flapjack.Test.CompileExpParity
