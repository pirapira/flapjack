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

def wordProgHasNotEqualZeroTest {α : Type} : WordProg α → Bool
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

/-! The same materialize/copy/test shape inside a Loop is the case that
    exercises the recursive descent of Cake's simp_duplicate_if. -/
def loopRoundTrip : WordProg Nat :=
  .loop []
    (.seq
      (.seq
        (.seq (.assign 4 (.var 6)) (.assign 10 (.var 2)))
        (.ite .less 4 (.reg 10)
          (.assign 4 (.const 1)) (.assign 4 (.const 0))))
      (.seq (.assign 8 (.var 4))
        (.ite .notEqual 8 (.imm 0) (.break 0) .skip))) []

def loopRoundTripFuses : Bool :=
  !wordProgHasNotEqualZeroTest (wordFuseConditions loopRoundTrip)

#guard loopRoundTripFuses

def nestedLoopRoundTrip : WordProg Nat :=
  .loop []
    (.seq (.assign 4 (.var 6))
      (.seq (.assign 10 (.var 2))
        (.ite .less 4 (.reg 10)
          (.seq (.assign 4 (.const 1))
            (.seq .tick
              (.seq (.assign 8 (.var 4))
                (.ite .notEqual 8 (.imm 0) (.break 0) .skip))))
          (.break 0)))) []

def nestedLoopRoundTripFuses : Bool :=
  !wordProgHasNotEqualZeroTest (wordFuseConditions nestedLoopRoundTrip)

#guard nestedLoopRoundTripFuses

def loopConditionMaterialization : WordProg Nat :=
  .loop []
    (.seq (.assign 4 (.var 6))
      (.seq (.assign 10 (.var 2))
        (.ite .less 4 (.reg 10)
          (.seq
            (.ite .notEqual 4 (.reg 10)
              (.assign 4 (.const 1)) (.assign 4 (.const 0)))
            (.seq .tick
              (.seq (.assign 8 (.var 4))
                (.ite .notEqual 8 (.imm 0) (.break 0) .skip))))
          (.break 0)))) []

def loopConditionMaterializationFuses : Bool :=
  !wordProgHasNotEqualZeroTest (wordFuseConditions loopConditionMaterialization)

#guard loopConditionMaterializationFuses

/-! Cake also descends through a conditional branch before reaching a
    handler call.  The source-shaped exception path uses exactly this shape:
    the comparison result overwrites its left operand, is copied into a
    handler temporary, and is then tested against zero. -/
def callHandlerRoundTrip : WordProg (RiscV.Word 64) :=
  .ite .equal 6 (.reg 12)
    (.call (some ([6], ([0, 8], []), .skip, 7, 4)) (some 6) []
      (some (12,
        (.seq
          (.ite .equal 10 (.reg 16)
            (.assign 10 (.const 1)) (.assign 10 (.const 0)))
          (.seq .tick
            (.seq (.assign 4 (.var 10))
              (.seq (.ite .notEqual 4 (.imm 0) .skip .skip) .tick)))),
        7, 5)))
    .skip

def callHandlerRoundTripFuses : Bool :=
  !wordProgHasNotEqualZeroTest
    (wordFuseConditionsWithFold callHandlerRoundTrip)

#guard callHandlerRoundTripFuses

def cakePreSsaRoundTrip : WordProg (RiscV.Word 64) :=
  wordToWordPreSsa
    (.seq (.ite .less 1 (.reg 2)
        (.assign 3 (.const 1)) (.assign 3 (.const 0)))
      (.seq (.assign 4 (.var 3))
        (.ite .notEqual 4 (.imm 0) (.assign 5 (.const 7)) .skip)))

def cakePreSsaRoundTripMatchesCake : Bool :=
  match wordProgToList cakePreSsaRoundTrip with
  | [.ite .less 1 (.reg 2)
      (.seq (.assign 3 (.const 1))
        (.seq (.assign 4 (.const 1))
          (.seq .skip (.assign 5 (.const 7)))))
      (.seq (.assign 3 (.const 0))
        (.seq (.assign 4 (.const 0)) (.seq .skip .skip)))] => true
  | _ => false

#guard cakePreSsaRoundTripMatchesCake

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
      ("fusion descends into Loop bodies", loopRoundTripFuses),
      ("fusion descends into conditional Loop branches",
        nestedLoopRoundTripFuses),
      ("fusion handles materialized conditions in Loop branches",
        loopConditionMaterializationFuses),
      ("Cake pre-SSA pass order keeps const propagation before fusion",
        cakePreSsaRoundTripMatchesCake),
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
