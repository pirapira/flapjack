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

def finiteMapLoadByteLocalOK : Bool :=
  match compileExpHOL finiteMapContext (.loadByte (.var .local "p")) with
  | ([.loadByte (.var 5)], .one) => true
  | _ => false

/-! This matches the direct HOL `loadbyte_recursive_address` row. It checks
    that LoadByte preserves the recursively compiled address expression. -/
def loadByteRecursiveAddressOK : Bool :=
  oneResultOK [.loadByte (.op .add [.const 1, .const 2])]
    (compileExpHOL finiteMapContext
      (.loadByte (.op .add [.const 1, .const 2])))

/-! The remaining probe rows are reproduced through the tagged finite-map
    `compileExpHOL`. These mirror the `compileExp` rows above but exercise the
    HOL-shaped path used by `compileProgHOL`/`compileProgRiscV`. -/
/-! Includes the direct HOL `bytes_in_word` constructor row in
    `compile_exp_probe.out`; the 64-bit value is separately pinned to `8w` by
    the original HOL word-boundary probe and `CrepRuntimeTargetParity`. -/
def holLeavesOK : Bool :=
  oneResultOK [.const 7] (compileExpHOL finiteMapContext (.const 7)) &&
  oneResultOK [.const 0] (compileExpHOL finiteMapContext (.var .global "g")) &&
  oneResultOK [.baseAddr] (compileExpHOL finiteMapContext (.baseAddr)) &&
  oneResultOK [.topAddr] (compileExpHOL finiteMapContext (.topAddr)) &&
  oneResultOK [.const CrepBytesInWord.bytesInWord]
    (compileExpHOL finiteMapContext .bytesInWord)

/-! These fallback outputs match direct HOL `nstruct` and `nfield` rows.
    Source stateRel simultaneously rules out a successful source evaluation
    with the empty PanSem struct table, so the full-IH proof cases are
    discharged from source semantics rather than treating the fallback as a
    successful translation. -/
def holNamedFallbackOK : Bool :=
  oneResultOK [.const 0] (compileExpHOL finiteMapContext (.nStruct "S" [])) &&
  oneResultOK [.const 0]
    (compileExpHOL finiteMapContext (.nField "x" (.const 1)))

/-! Direct HOL `load_one` observation for `Load One (Const 3w)` in
    `compile_exp_probe.out`. -/
def holLoadOneOK : Bool :=
  oneResultOK [.load (.const 3)]
    (compileExpHOL finiteMapContext (.load .one (.const 3)))

/-! Direct HOL `load_two` observation for a two-word flat Load in
    `compile_exp_probe.out`. At RV64 its second compiled Load uses stride 8. -/
def holLoadTwoOK : Bool :=
  match compileExpHOL finiteMapContext
      (.load (.comb [.one, .one]) (.const 3)) with
  | ([.load (.const 3), .load (.op .add [.const 3, .const 8])],
      .comb [.one, .one]) => true
  | _ => false

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

/-! This mirrors the direct HOL `op_nary` fixture and pins the original
    compile_exp list-preserving case at arity three. -/
def holNaryOpOK : Bool :=
  oneResultOK [.op .add [.const 1, .const 2, .const 3]]
    (compileExpHOL finiteMapContext (.op .add [.const 1, .const 2, .const 3]))

def holCmpShiftOK : Bool :=
  oneResultOK [.cmp .equal (.const 1) (.const 0)]
      (compileExpHOL finiteMapContext (.cmp .equal (.const 1) (.const 0))) &&
  oneResultOK [.shift .lsl (.const 2) (.const 1)]
      (compileExpHOL finiteMapContext (.shift .lsl (.const 2) (.const 1)))

def parityGuard : Bool :=
  leavesOK && structFieldOK && loadsOpsOK && cmpShiftOK && finiteMapLookupOK &&
  finiteMapLoad32LocalOK && finiteMapLoadByteLocalOK && loadByteRecursiveAddressOK &&
  holLeavesOK && holNamedFallbackOK && holLoadOneOK && holLoadTwoOK &&
  holStructFieldOK && holLoadsOpsOK &&
  holNaryOpOK && holCmpShiftOK

example : compileExpHOL finiteMapContext (.load32 (.var .local "p")) =
    ([.load32 (.var 5)], .one) := by
  simp [compileExpHOL, finiteMapContext, FLOOKUP, FUPDATE]

example : compileExpHOL finiteMapContext (.loadByte (.var .local "p")) =
    ([.loadByte (.var 5)], .one) := by
  simp [compileExpHOL, finiteMapContext, FLOOKUP, FUPDATE]

example : compileExpHOL finiteMapContext
    (.loadByte (.op .add [.const 1, .const 2])) =
      ([.loadByte (.op .add [.const 1, .const 2])], .one) := by
  simp [compileExpHOL, compileExpHOL.compileExpListHOL, cexpHeads,
    finiteMapContext]

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

/-- The width-indexed delegation `compileExpHOLW` (whose `compile_exp_def` tag
    is withdrawn as a documented carrier mismatch) is definitionally the generic
    `compileExpHOL` instantiated at the `BitVec` carrier. -/
example (context : PanToCrepHOLContext (BitVec 64)) (expression : Exp (BitVec 64)) :
    compileExpHOLW context expression = compileExpHOL context expression := rfl

/-! Bridge-only fixture (`flapjack-pxn.18.3.1.3.2`): the shipped RV64 path
    `compileProgRiscV`/`compileProgHOL` still executes the generic
    `compileExpHOL`, which at the word carrier is definitionally the
    width-indexed `compileExpHOLW` by `compileExpHOLW_eq_compileExpHOL`. That
    delegation's `compile_exp_def` tag stays withdrawn (documented carrier
    mismatch). This is NOT textual routing: production does not call it, and the
    production-path rule is therefore not met (full routing tracked by
    `flapjack-pxn.18.3.5.3.1.2`). The rows below re-check the direct HOL oracle
    (`scripts/hol-probes/compile_exp_probe.out`) through `compileExpHOLW` at the
    `BitVec 64` carrier. -/
def riscvContext : PanToCrepHOLContext (BitVec 64) :=
  { vars := FUPDATE (FUPDATE FEMPTY ("p", (.one, [3]))) ("p", (.one, [5]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 5 }

def holWOneOK (expected : List (CrepExp (BitVec 64))) :
    List (CrepExp (BitVec 64)) × Shape → Bool
  | (actual, .one) => actual == expected
  | _ => false

def holWCombTwoOK (expected : List (CrepExp (BitVec 64))) :
    List (CrepExp (BitVec 64)) × Shape → Bool
  | (actual, .comb [.one, .one]) => actual == expected
  | _ => false

def holWParityOK : Bool :=
  holWOneOK [.const 7] (compileExpHOLW riscvContext (.const 7)) &&
  holWOneOK [.var 5] (compileExpHOLW riscvContext (.var .local "p")) &&
  holWOneOK [.load32 (.var 5)]
    (compileExpHOLW riscvContext (.load32 (.var .local "p"))) &&
  holWOneOK [.op .add [.const 1, .const 2]]
    (compileExpHOLW riscvContext (.op .add [.const 1, .const 2])) &&
  holWCombTwoOK [.load (.const 3), .load (.op .add [.const 3, .const 8])]
    (compileExpHOLW riscvContext (.load (.comb [.one, .one]) (.const 3)))

example : compileExpHOLW riscvContext (.load32 (.var .local "p")) =
    ([.load32 (.var 5)], .one) := by
  simp [compileExpHOLW, compileExpHOL, riscvContext, FLOOKUP, FUPDATE]

example (context : PanToCrepHOLContext (BitVec 64)) (expression : Exp (BitVec 64)) :
    compileExpHOLW context expression = compileExpHOL context expression :=
  compileExpHOLW_eq_compileExpHOL context expression

#eval holWParityOK
#guard holWParityOK

end Flapjack.Test.CompileExpParity
