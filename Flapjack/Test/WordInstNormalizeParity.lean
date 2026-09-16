import Flapjack.RiscV.WordInstSelect

/-!
# Cake `pull_exp`/`flatten_exp` constant-placement oracle (GH #1024)

Cake's instruction selection normalizes every assignment operand with

```
inst_select c temp (Assign v exp) =
  (inst_select_exp c v temp o flatten_exp o pull_exp) exp
```

(`cakeml/compiler/backend/word_instScript.sml:383`).  The two passes interact:

* `pull_ops` collects operands with `ls ++ acc`, which reverses their order.
* `optimize_consts`/`reduce_const` fold constant operands into a single
  constant and place it at the front of the collected list (and, when there
  are no constants, they reverse the list).
* `flatten_exp (Op op (x::xs)) = Op op [flatten_exp (Op op xs); flatten_exp x]`
  is head-last, which reverses once more.

The net effect, confirmed by the direct HOL evaluation in
`scripts/hol-probes/word_inst_probe.out`, is that a plain operation keeps the
reversed `pull_ops` order (`Op Add [Var 2; Var 4]` normalizes to
`Op Add [Var 4; Var 2]`) while a constant operand ends up **last**
(`Op Add [Var 7; Const 1w]` and `Op Add [Const 1w; Var 7]` both normalize to
`Op Add [Var 7; Const 1w]`).  `inst_select_exp` only uses an immediate when the
second operand is a constant, so this is exactly the `addi` shape.

The port keeps Cake's constant-right `convert_sub` and head-first
`wordInstFlattenExp`; `wordInstConstantsToEnd` reproduces Cake's constant
placement (constants last) and, for `Add`, Cake's `optimize_consts` folding of
several constants into one value together with `reduce_const`'s zero drop.

This module pins the oracle values from `word_inst_probe.out` and checks that
the port's normalizer reaches them.
-/

namespace Flapjack.Test.WordInstNormalizeParity

open Flapjack Flapjack.RiscV

/-- In-order atoms of an `Op Add` spine: `some name` for a variable, `none`
for a constant. -/
def addOperandAtoms : WordExp α → List (Option Nat)
  | .op .add arguments => List.flatMap addOperandAtoms arguments
  | .var name => [some name]
  | .const _ => [none]
  | _ => []

/-- `word_inst_probe.out: norm_two_vars`. -/
def cakeTwoVarAtoms : List (Option Nat) := [some 4, some 2]

/-- `word_inst_probe.out: norm_t_plus_1` / `norm_1_plus_t`. -/
def cakeVarConstAtoms : List (Option Nat) := [some 7, none]

/-- `word_inst_probe.out: norm_nested_add`. -/
def cakeNestedAtoms : List (Option Nat) := [some 2, some 1, none]

/-- `word_inst_probe.out: norm_const_middle`. -/
def cakeConstMiddleAtoms : List (Option Nat) := [some 3, some 1, none]

/-- Does `expression` have the shape `Op Add [Var _, Const value]`? -/
def addVarConstValueShape [BEq α] (value : α) : WordExp α → Bool
  | .op .add args =>
      match args with
      | [a, b] =>
          (match a with | .var _ => true | _ => false) &&
          (match b with | .const other => other == value | _ => false)
      | _ => false
  | _ => false

/-- The port reverses plain operand order exactly like `pull_ops` + flatten. -/
def twoVarOrderMatches : Bool :=
  addOperandAtoms
      (wordInstNormalizeExp (α := Nat) (.op .add [.var 2, .var 4]))
    == cakeTwoVarAtoms

/-- A source constant-second `t + 1` keeps the constant second. -/
def varConstOrderMatches : Bool :=
  addOperandAtoms
      (wordInstNormalizeExp (α := Nat) (.op .add [.var 7, .const 1]))
    == cakeVarConstAtoms

/-- A source constant-first `1 + t` also normalizes the constant second. -/
def constFirstOrderMatches : Bool :=
  addOperandAtoms
      (wordInstNormalizeExp (α := Nat) (.op .add [.const 1, .var 7]))
    == cakeVarConstAtoms

/-- A nested addition keeps the constant last. -/
def nestedOrderMatches : Bool :=
  addOperandAtoms
      (wordInstNormalizeExp (α := Nat)
        (.op .add [.var 1, .op .add [.var 2, .const 3]]))
    == cakeNestedAtoms

/-- `word_inst_probe.out: norm_nested_fixture`: the five-load nested add
    used by the exact nested-expression corpus fixture. -/
def cakeNestedFixtureAtoms : List (Option Nat) :=
  [some 4, some 2, some 10, some 12, some 6]

def nestedFixtureOrderMatches : Bool :=
  addOperandAtoms
      (wordInstNormalizeExp (α := Nat)
        (.op .add [.var 6,
          .op .add [.var 4,
            .op .add [.var 12,
              .op .add [.var 2, .var 10]]]]))
    == cakeNestedFixtureAtoms

/-- A constant in the middle is moved after the variables. -/
def constMiddleOrderMatches : Bool :=
  addOperandAtoms
      (wordInstNormalizeExp (α := Nat)
        (.op .add [.var 1, .const 5, .var 3]))
    == cakeConstMiddleAtoms

/-- `word_inst_probe.out: optimize_consts_two_consts` composed with flatten:
`1 + 2 + t` folds to `t + 3` with the constant second. -/
def foldTwoConstantsMatches : Bool :=
  addOperandAtoms
      (wordInstNormalizeExp (α := Nat)
        (.op .add [.const 1, .const 2, .var 3]))
    == [some 3, none]

/-- `word_inst_probe.out: optimize_consts_zero_add` / `reduce_const_add_zero_tail`:
`0 + t` drops the identity constant and normalizes to `t`. -/
def zeroConstantDropped : Bool :=
  addOperandAtoms
      (wordInstNormalizeExp (α := Nat) (.op .add [.const 0, .var 3]))
    == [some 3]

/-- `word_inst_probe.out: norm_nested_add_consts`: an all-constant `Add`
normalizes to the folded constant `0`. -/
def allConstantAddFolds : Bool :=
  match wordInstNormalizeExp (α := Nat) (.op .add [.const 0, .const 0]) with
  | .const value => value == 0
  | _ => false

/-- `x - 8` is `x + (-8)` with the constant second, like Cake's `convert_sub`
composed with the constant placement. -/
def subtractionConstantSecond : Bool :=
  addVarConstValueShape ((0 : BitVec 64) - 8)
    (wordInstNormalizeExp (α := BitVec 64) (.op .sub [.var 7, .const 8]))

/-- `word_inst_probe.out: optimize_consts_or_zero` / `norm_or_zero`: the `0w`
identity is dropped for `Or` exactly as for `Add`. -/
def orZeroConstantDropped : Bool :=
  addOperandAtoms
      (wordInstNormalizeExp (α := Nat) (.op .or [.const 0, .var 3]))
    == [some 3]

/-- `word_inst_probe.out: optimize_consts_xor_zero`: the `0w` identity is also
dropped for `Xor`. -/
def xorZeroConstantDropped : Bool :=
  addOperandAtoms
      (wordInstNormalizeExp (α := Nat) (.op .xor [.const 0, .var 3]))
    == [some 3]

/-- `word_inst_probe.out: optimize_consts_and_zero` / `norm_and_zero`:
`reduce_const And 0w rest = Const 0w` collapses the whole expression. -/
def andZeroConstantCollapses : Bool :=
  match wordInstNormalizeExp (α := Nat) (.op .and [.const 0, .var 3]) with
  | .const value => value == 0
  | _ => false

/-! Cake's `word_to_word$compile_single` passes the normalized Word program
    directly to `inst_select`; the source-facing flatten adapter must not
    insert a fresh assignment before this nested shift. -/
def nestedSelectorBoundaryMatches : Bool :=
  let program : WordProg Nat :=
    .assign 20 (.shift .lsl (.op .add [.var 6, .var 4]) (.const 1))
  match wordFlattenProgramFrom program with
  | .assign 20 (.shift .lsl (.op .add [.var 6, .var 4]) (.const 1)) => true
  | _ => false

/- Cake's `inst_select_exp (Shift _ exp (Var n))` materializes both operands
   and emits an arithmetic shift with the second temporary as a register. -/
def variableShiftSelectorMatches : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 14 (.shift .asr (.var 18) (.var 22))) with
  | .seq (.move 0 [(23, 18)])
      (.seq (.move 0 [(24, 22)])
        (.inst (.arith (.shift .asr 14 23 (.reg 24))))) => true
  | _ => false

def constantSelectorMatches : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 18 (.const 7)) with
  | .inst (.const 18 7) => true
  | _ => false

def loadSelectorMatches : Bool :=
  match wordInstSelectProgram (α := Nat) 23
      (.assign 14 (.load (.var 18))) with
  | .seq (.move 0 [(23, 18)]) (.inst (.mem .load 14 23)) => true
  | _ => false

#guard twoVarOrderMatches
#guard varConstOrderMatches
#guard constFirstOrderMatches
#guard nestedOrderMatches
#guard nestedFixtureOrderMatches
#guard constMiddleOrderMatches
#guard foldTwoConstantsMatches
#guard zeroConstantDropped
#guard allConstantAddFolds
#guard subtractionConstantSecond
#guard orZeroConstantDropped
#guard xorZeroConstantDropped
#guard andZeroConstantCollapses
#guard nestedSelectorBoundaryMatches
#guard variableShiftSelectorMatches
#guard constantSelectorMatches
#guard loadSelectorMatches

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("the Cake normalization oracle keeps the reversed two-variable order", twoVarOrderMatches)
    , ("a source t + 1 normalizes with the constant second like Cake", varConstOrderMatches)
    , ("a source 1 + t also normalizes the constant second", constFirstOrderMatches)
    , ("a nested addition keeps the constant last like Cake", nestedOrderMatches)
    , ("a constant in the middle moves after the variables", constMiddleOrderMatches)
    , ("x - 8 normalizes to x + (-8) with the constant second", subtractionConstantSecond)
    , ("several constants fold into one value with the constant second", foldTwoConstantsMatches)
    , ("a zero constant is dropped like Cake reduce_const", zeroConstantDropped)
    , ("an all-constant addition folds to the constant", allConstantAddFolds)
    , ("the Or zero identity is dropped like Cake reduce_const", orZeroConstantDropped)
    , ("the Xor zero identity is dropped like Cake reduce_const", xorZeroConstantDropped)
    , ("the And zero fold collapses to the constant like Cake reduce_const", andZeroConstantCollapses)
    , ("the source selector boundary preserves Cake's nested expression shape", nestedSelectorBoundaryMatches)
    , ("a variable shift uses Cake's two operand moves and register shift", variableShiftSelectorMatches)
    , ("a constant assignment becomes Cake's Const instruction", constantSelectorMatches)
    , ("a load becomes Cake's memory instruction after its address move", loadSelectorMatches)
  ]
  let mut ok := true
  for (label, passed) in checks do
    if passed then
      IO.println s!"PASS {label}"
    else
      IO.println s!"FAIL {label}"
      ok := false
  pure ok

end Flapjack.Test.WordInstNormalizeParity
