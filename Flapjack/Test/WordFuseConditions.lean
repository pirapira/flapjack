import Flapjack.RiscV.WordFuseConditions

open Flapjack Flapjack.RiscV

namespace Flapjack.Test.WordFuseConditions

/-- The materialize-then-test round trip that `CrepToLoop` emits for a
relational condition: an `ite` writes 1/0 into `3`, the value is copied to
`4`, and the branch tests `4 != 0`. -/
def roundTrip : WordProg Nat :=
  .seq (.ite .less 1 (.reg 2) (.assign 3 (.const 1)) (.assign 3 (.const 0)))
    (.seq (.assign 4 (.var 3))
      (.ite .notEqual 4 (.imm 0) (.assign 5 (.const 7)) .skip))

def wordProgHasNotEqualZeroTest : WordProg Nat → Bool
  | .seq first second =>
      wordProgHasNotEqualZeroTest first || wordProgHasNotEqualZeroTest second
  | .ite .notEqual _ (.imm _) _ _ => true
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgHasNotEqualZeroTest thenBranch ||
        wordProgHasNotEqualZeroTest elseBranch
  | _ => false

def wordProgHasDirectLessTest : WordProg Nat → Bool
  | .seq first second =>
      wordProgHasDirectLessTest first || wordProgHasDirectLessTest second
  | .ite .less _ _ thenBranch elseBranch =>
      wordProgHasDirectLessTest thenBranch ||
        wordProgHasDirectLessTest elseBranch
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgHasDirectLessTest thenBranch ||
        wordProgHasDirectLessTest elseBranch
  | _ => false

/-- The pass rewrites the `notEqual 4 0` test into the original `less 1 2`
comparison, keeping the 1/0 definition and the copy in place. -/
def fusedProgram : WordProg Nat := wordFuseConditions roundTrip

def fusedProgramStatements : List (WordProg Nat) := wordProgToList fusedProgram

/-- The fused program keeps the materialized definition and the copy but the
third statement now branches directly on the original `less 1 2`. -/
def fusedProgramShapeMatches : Bool :=
  match fusedProgramStatements with
  | [.ite .less 1 (.reg 2) (.assign 3 (.const 1)) (.assign 3 (.const 0)),
     .assign 4 (.var 3),
     .ite .less 1 (.reg 2) (.assign 5 (.const 7)) .skip] => true
  | _ => false

def roundTripNeedsFusion : Bool :=
  wordProgHasNotEqualZeroTest roundTrip

def fusedProgramUsesDirectBranch : Bool :=
  fusedProgramShapeMatches && !wordProgHasNotEqualZeroTest fusedProgram

/-! The source pipeline can leave harmless `Skip` wrappers around the branch
    definitions and between the copy and the test.  Cake's `Seq_assoc` removes
    those wrappers before this rewrite; keep this shape covered as well. -/
def roundTripWithSkips : WordProg Nat :=
  .seq (.ite .less 1 (.reg 2)
      (.seq (.assign 3 (.const 1)) .skip)
      (.seq (.assign 3 (.const 0)) .skip))
    (.seq .tick
      (.seq (.assign 4 (.var 3))
        (.seq .skip
          (.ite .notEqual 4 (.imm 0) (.assign 5 (.const 7)) .skip))))

def skippedRoundTripFuses : Bool :=
  !wordProgHasNotEqualZeroTest (wordFuseConditions roundTripWithSkips)

#guard skippedRoundTripFuses

def terminatingElseIsPushedOut : Bool :=
  match wordPushOutIf
      (.ite .less 1 (.reg 2) (.assign 3 (.var 4)) (.raise 0) : WordProg Nat) with
  | .seq (.ite .less 1 (.reg 2) .skip (.raise 0)) (.assign 3 (.var 4)) => true
  | _ => false

#guard terminatingElseIsPushedOut

#guard roundTripNeedsFusion
#guard fusedProgramUsesDirectBranch

/-- When the materialisation overwrites the comparison operand, the pass uses
Cake's duplicate-if shape instead of retesting the overwritten value. -/
def clobberingRoundTrip : WordProg Nat :=
  .seq (.ite .less 2 (.reg 3) (.assign 2 (.const 1)) (.assign 2 (.const 0)))
    (.seq (.assign 4 (.var 2))
      (.ite .notEqual 4 (.imm 0) (.assign 5 (.const 7)) .skip))

def operandClobberIsFused : Bool :=
  match wordFuseConditions clobberingRoundTrip with
  | .ite .less 2 (.reg 3) _ _ =>
      !wordProgHasNotEqualZeroTest (wordFuseConditions clobberingRoundTrip)
  | _ => false

#guard operandClobberIsFused

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("the CrepToLoop round trip materialises then retests the condition",
        roundTripNeedsFusion),
      ("the fusion pass restores the Cake direct branch", 
        fusedProgramUsesDirectBranch),
      ("fusion removes harmless source Seq/Skip wrappers",
        skippedRoundTripFuses),
      ("Cake terminating conditional branches are pushed out",
        terminatingElseIsPushedOut),
      ("a clobbering materialisation uses Cake duplicate-if",
        operandClobberIsFused) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.WordFuseConditions
