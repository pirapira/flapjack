import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.Proofs.PanSimp
import Flapjack.Pancake.Proofs.PanSimp.Evaluate
import Flapjack.Pancake.PanGlobals
import Flapjack.PanValueFfiEventMonotonicity
import Flapjack.PanValueFfiClockShift
import Flapjack.PanValueFfiClockCorrectness

namespace Flapjack.Test.PanSimpParity

open Flapjack

def evaluatorContext : PanValueFfiContext Nat :=
  { sharedDomain := fun _ => true
    byteAlign := id
    bigEndian := false
    wordToBytes := fun value _ => [UInt8.ofNat value]
    wordOfBytes := fun _ bytes =>
      match bytes with
      | byte :: _ => byte.toNat
      | [] => 0
    wordToByte := fun value => UInt8.ofNat value
    byteToWord := fun byte => byte.toNat
    valueToNat := id }

def evaluatorHandler : PanValueStatefulFfiHandler Nat Unit :=
  fun _ _ _ _ _ locals ffi => some (locals, ffi)

def evaluatorFfi : FfiState Unit :=
  { oracle := fun _ state _ _ => .returned state []
    state := ()
    ioEvents := [] }

theorem clocked_seq_skip_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.seq .skip .skip) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 0 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 .skip := by
  exact evalPanValueFfiClockProg_seq_skip evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 0 1
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi .skip

theorem clocked_skip_seq_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.seq .skip .skip) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 0 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 .skip := by
  exact evalPanValueFfiClockProg_skip_seq evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 0 1
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi .skip

theorem clocked_while_body_same_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.while (.const 0) .skip) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.while (.const 0) (.annot "tag" "text")) := by
  have hsame := evalPanValueFfiClockProg_while_body_same evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 (.const 0) .skip
    (.annot "tag" "text") (hbody := by
      intro fuel clock locals globals memory ffi memoryAccess contracts memoryHandler
      cases fuel with
      | zero => simp [evalPanValueFfiClockProg]
      | succ fuel =>
          simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
            evalPanValueFfiProgSteps])
  exact hsame 2 1 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi none none none

theorem clocked_while_success_requires_body_success
    (result : PanValueFfiClockResult Nat Unit)
    (hresult : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.while (.const 1) .skip) = some result) :
    ∃ bodyResult,
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
        evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
        (fun _ => none) evaluatorFfi 0 .skip = some bodyResult := by
  apply evalPanValueFfiClockProg_while_some_implies_body_some
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    (.const 1) .skip 1 1 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi none none none 1
  · simp [evalPanValueExp]
  · decide
  · decide
  · exact hresult

theorem clocked_seq_success_requires_first_success
    (hresult : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.seq .skip .skip) ≠ none) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 .skip ≠ none := by
  apply evalPanValueFfiClockProg_seq_no_none evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 1 1
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi .skip .skip
    none none none
  exact hresult

theorem clocked_while_nonzero_requires_body_success
    (hresult : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.while (.const 1) .skip) ≠ none) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 0 .skip ≠ none := by
  apply evalPanValueFfiClockProg_while_no_none evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    1 1 (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi
    (.const 1) .skip 1 none none none
  · simp [evalPanValueExp]
  · decide
  · decide
  · exact hresult

theorem clocked_seq_first_congr_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.seq .skip .tick) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.seq (.annot "tag" "text") .tick) := by
  apply evalPanValueFfiClockProg_seq_congr evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 1 1
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi
    .skip (.annot "tag" "text") .tick none none none
  simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
    evalPanValueFfiProgSteps]

theorem clocked_seq_second_congr_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.seq .tick .skip) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.seq .tick (.annot "tag" "text")) := by
  apply evalPanValueFfiClockProg_seq_congr_second evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 1 1
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi
    .tick .skip (.annot "tag" "text") none none none
  intro fuel clock locals globals memory ffi
  cases fuel with
  | zero => simp [evalPanValueFfiClockProg]
  | succ fuel =>
      simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
        evalPanValueFfiProgSteps]

/-! A common upper fuel restores the semantic equality after the explicit
    fixed-fuel gap witness: the transformed side succeeds at fuel 2, while
    the original sequence needs fuel 4, and both agree once lifted to 4. -/
theorem clocked_seq_assoc_common_fuel_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 4 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (seqAssoc (.skip : Prog Nat) (.seq .skip (.seq .skip .skip))) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 4 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.seq .skip (.seq .skip (.seq .skip .skip))) := by
  apply evalPanValueFfiClockProg_seqAssoc_eq_of_common_fuel
    (fuelLeft := 2) (fuelRight := 4) (commonFuel := 4)
    (result := (.control (.normal (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi), 1))
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    (.skip : Prog Nat) (.seq .skip (.seq .skip .skip))
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    none none none
  · simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
      evalPanValueFfiProgSteps, seqAssoc]
  · simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
      evalPanValueFfiProgSteps]
  · decide
  · decide

/-- The structural budget alone makes the `Skip`/`Seq` fragment succeed, with no
    external successful-run witness. -/
theorem clocked_seq_skip_fragment_budget_succeeds :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 3 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.seq (.skip : Prog Nat) (.seq .skip .skip)) none none none =
    some (.control (.normal (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi), 1) := by
  exact evalPanValueFfiClockProg_seqSkipFragment_some evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 3 (fun _ => none)
    (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.seq (.skip : Prog Nat) (.seq .skip .skip)) none none none
    (PanSimpSeqSkipFragment.seq .skip (.seq .skip .skip)
      PanSimpSeqSkipFragment.skip
      (PanSimpSeqSkipFragment.seq .skip .skip
        PanSimpSeqSkipFragment.skip PanSimpSeqSkipFragment.skip))
    (by simp [panSimpSeqSkipFuel])

/-- The `Seq` composition law at the call-aware budget, exercised on two
    `Skip` leaves whose component budgets are lifted to the common fuel. -/
theorem clocked_seq_progCallFuel_composes :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (progCallFuel 7 (.seq (.skip : Prog Nat) (.skip : Prog Nat)))
      (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.seq (.skip : Prog Nat) (.skip : Prog Nat)) none none none =
    some (.control (.normal (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi), 1) := by
  have hskip := evalPanValueFfiClockProg_leaf_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 (.skip : Prog Nat)
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none none none
    PanValueFfiLeafProg.skip
    (.normal (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi) 1
    (by simp [evalPanValueFfiProgSteps])
  have hfirst := evalPanValueFfiClockProg_fuel_mono evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    (fuel := progCallFuel 7 (.skip : Prog Nat))
    (fuel' := progCallFuel 7 (.skip : Prog Nat) + progCallFuel 7 (.skip : Prog Nat))
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 (.skip : Prog Nat)
    none none none (by simp [progCallFuel]) hskip
  exact evalPanValueFfiClockProg_seq_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 (.skip : Prog Nat) (.skip : Prog Nat)
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none none none
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi)) 1
    hfirst (by simpa using hfirst)

/-- The same `Skip`/`Seq` fragment succeeds at the call-aware budget
    `progCallFuel`, which dominates the fragment budget. -/
theorem clocked_seq_skip_fragment_progCallFuel_succeeds :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (progCallFuel 7 (.seq (.skip : Prog Nat) (.seq .skip .skip)))
      (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.seq (.skip : Prog Nat) (.seq .skip .skip)) none none none =
    some (.control (.normal (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi), 1) := by
  exact evalPanValueFfiClockProg_seqSkipFragment_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 (fun _ => none)
    (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.seq (.skip : Prog Nat) (.seq .skip .skip)) none none none
    (PanSimpSeqSkipFragment.seq .skip (.seq .skip .skip)
      PanSimpSeqSkipFragment.skip
      (PanSimpSeqSkipFragment.seq .skip .skip
        PanSimpSeqSkipFragment.skip PanSimpSeqSkipFragment.skip))

/-! The fuel-adequacy formulation of the same rewrite: on the `Skip`/`Seq`
    fragment the structural budget alone guarantees success, so the common-fuel
    equality follows from `panSimpSeqSkipFuel` bounds rather than an explicit
    successful-run witness. -/
theorem clocked_seq_assoc_fragment_budget_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 3 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (seqAssoc (.skip : Prog Nat) (.seq .skip .skip)) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 3 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.seq (.skip : Prog Nat) (.seq .skip .skip)) := by
  apply evalPanValueFfiClockProg_seqAssoc_eq_of_seqSkipFragment
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    (.skip : Prog Nat) (.seq .skip .skip) 3
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    none none none
  · exact PanSimpSeqSkipFragment.skip
  · exact PanSimpSeqSkipFragment.seq .skip .skip
      PanSimpSeqSkipFragment.skip PanSimpSeqSkipFragment.skip
  · simp [seqAssoc, panSimpSeqSkipFuel]
  · simp [panSimpSeqSkipFuel]

/-- The same `seqAssoc` equality stated directly on the additive fuel foundation
    `panSimpSkipSeqProg`/`panSimpSkipSeqFuel`, at the common budget
    `panSimpSkipSeqFuel pre + panSimpSkipSeqFuel program + 1`. -/
theorem clocked_seq_assoc_skip_seq_fuel_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 5 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (seqAssoc (.skip : Prog Nat) (.seq .skip .skip)) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 5 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.seq (.skip : Prog Nat) (.seq .skip .skip)) := by
  exact evalPanValueFfiClockProg_seqAssoc_eq_of_skipSeqProg
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    (.skip : Prog Nat) (.seq .skip .skip)
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    none none none (by trivial) (by constructor <;> trivial)

/-- On the `Skip`/`Seq` fragment `retToTail` is the identity. -/
example : retToTail (.seq (.skip : Prog Nat) .skip) = .seq .skip .skip := by
  rw [PanSimpSeqSkipFragment_retToTail]
  exact PanSimpSeqSkipFragment.seq .skip .skip
    PanSimpSeqSkipFragment.skip PanSimpSeqSkipFragment.skip

/-- Cake's `compile_correct_same_state` on the `Skip`/`Seq` fragment: the full
    `panSimpProg` transform and the source program agree once the common fuel
    dominates both structural budgets. -/
theorem clocked_pan_simp_prog_fragment_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 3 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (panSimpProg (.seq (.skip : Prog Nat) .skip)) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 3 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.seq (.skip : Prog Nat) .skip) := by
  apply evalPanValueFfiClockProg_panSimpProg_eq_of_seqSkipFragment
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    (.seq (.skip : Prog Nat) .skip) 3
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    none none none
  · exact PanSimpSeqSkipFragment.seq .skip .skip
      PanSimpSeqSkipFragment.skip PanSimpSeqSkipFragment.skip
  · simp [panSimpProg, seqAssoc, retToTail, panSimpSeqSkipFuel]
  · simp [panSimpSeqSkipFuel]

/-- `Annot` is transparent to the clocked evaluator. -/
example : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
    [] [] 0 0 8 1 (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.annot "tag" "text") =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 1) := by
  exact evalPanValueFfiClockProg_annot_some evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 0 (fun _ => none) (fun _ => none) (fun _ => none)
    evaluatorFfi 1 "tag" "text" none none none

/-- A `Tick` with a nonzero clock succeeds and consumes one clock unit. -/
example : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
    [] [] 0 0 8 1 (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.tick : Prog Nat) =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 0) := by
  exact evalPanValueFfiClockProg_tick_some evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 0 (fun _ => none) (fun _ => none) (fun _ => none)
    evaluatorFfi 1 none none none (by decide)

/-- Compositional success of `Seq`: the second component starts from the first
    component's post-state and clock. -/
example : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
    [] [] 0 0 8 2 (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.seq (.annot "tag" "text") (.tick : Prog Nat)) =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 0) := by
  exact evalPanValueFfiClockProg_seq_some evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none) (fun _ => none)
    evaluatorFfi 1 (.annot "tag" "text") (.tick : Prog Nat) none none none
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi)) 0
    (evalPanValueFfiClockProg_annot_some evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 0 (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi 1 "tag" "text" none none none)
    (evalPanValueFfiClockProg_tick_some evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 0 (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi 1 none none none (by decide))

/-- A `While` whose condition is zero terminates immediately. -/
example : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
    [] [] 0 0 8 1 (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.while (.const 0) (.skip : Prog Nat)) =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 1) := by
  exact evalPanValueFfiClockProg_while_zero_some evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 0 (fun _ => none) (fun _ => none) (fun _ => none)
    evaluatorFfi 1 (.const 0) (.skip : Prog Nat) none none none 0
    (by simp [evalPanValueExp]) (by decide)

/-- `Dec` binds the value, runs the body under the updated local map, and
    restores the shadowed local. -/
example : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
    [] [] 0 0 8 2 (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.dec "x" .one (.const 5) (.annot "tag" "text")) =
    some (panValueFfiClockRestoreLocal "x" none
      (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
        (fun _ => none) (fun _ => none) evaluatorFfi)), 1) := by
  exact evalPanValueFfiClockProg_dec_some evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none) (fun _ => none)
    evaluatorFfi 1 "x" .one (.const 5) (.annot "tag" "text") none none none
    (.word 5)
    (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
      (fun _ => none) (fun _ => none) evaluatorFfi)) 1
    (by simp [evalPanValueExp]) (by simp [panValueShape, panShapeMatches])
    (evalPanValueFfiClockProg_annot_some evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 0 (updatePanValueMap (fun _ => none) "x" (.word 5))
      (fun _ => none) (fun _ => none) evaluatorFfi 1 "tag" "text" none none none)

/-- The same `Dec` at its own `progSize` budget (no free fuel parameter). -/
example : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
    [] [] 0 0 8 (progSize (.dec "x" .one (.const 5) (.annot "tag" "text")))
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.dec "x" .one (.const 5) (.annot "tag" "text")) =
    some (panValueFfiClockRestoreLocal "x" none
      (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
        (fun _ => none) (fun _ => none) evaluatorFfi)), 1) := by
  exact evalPanValueFfiClockProg_dec_some_progSize evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 (fun _ => none) (fun _ => none) (fun _ => none)
    evaluatorFfi 1 "x" .one (.const 5) (.annot "tag" "text") none none none
    (.word 5)
    (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
      (fun _ => none) (fun _ => none) evaluatorFfi)) 1
    (by simp [evalPanValueExp]) (by simp [panValueShape, panShapeMatches])
    (by
      simpa only [progSize] using
        (evalPanValueFfiClockProg_annot_some evaluatorContext (fun _ _ => none)
          evaluatorHandler [] [] 0 0 8 0 (updatePanValueMap (fun _ => none) "x" (.word 5))
          (fun _ => none) (fun _ => none) evaluatorFfi 1 "tag" "text" none none none))

/-- The same `Dec` at the call-aware budget, whose body budget is
    `progCallFuel 7 body`. -/
example : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
    [] [] 0 0 8 (progCallFuel 7 (.dec "x" .one (.const 5) (.annot "tag" "text")))
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.dec "x" .one (.const 5) (.annot "tag" "text")) =
    some (panValueFfiClockRestoreLocal "x" none
      (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
        (fun _ => none) (fun _ => none) evaluatorFfi)), 1) := by
  exact evalPanValueFfiClockProg_dec_some_progCallFuel evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 7 (fun _ => none) (fun _ => none) (fun _ => none)
    evaluatorFfi 1 "x" .one (.const 5) (.annot "tag" "text") none none none
    (.word 5)
    (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
      (fun _ => none) (fun _ => none) evaluatorFfi)) 1
    (by simp [evalPanValueExp]) (by simp [panValueShape, panShapeMatches])
    (by
      simpa only [progCallFuel] using
        (evalPanValueFfiClockProg_annot_some evaluatorContext (fun _ _ => none)
          evaluatorHandler [] [] 0 0 8 0 (updatePanValueMap (fun _ => none) "x" (.word 5))
          (fun _ => none) (fun _ => none) evaluatorFfi 1 "tag" "text" none none none))

/-- A nonzero `Ite` condition selects the then-branch. -/
example : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
    [] [] 0 0 8 2 (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.ite (.const 5) (.annot "tag" "text") (.tick : Prog Nat)) =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 1) := by
  exact evalPanValueFfiClockProg_ite_true_some evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none) (fun _ => none)
    evaluatorFfi 1 (.const 5) (.annot "tag" "text") (.tick : Prog Nat) none none none
    5 (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi)) 1
    (by simp [evalPanValueExp]) (by decide)
    (evalPanValueFfiClockProg_annot_some evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 0 (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi 1 "tag" "text" none none none)

/-- The same nonzero `Ite` at its own `progSize` budget (no free fuel parameter);
    the branch is evaluated at the combined `progSize` branch budget. -/
example : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
    [] [] 0 0 8 (progSize (.ite (.const 5) (.annot "tag" "text") (.tick : Prog Nat)))
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.ite (.const 5) (.annot "tag" "text") (.tick : Prog Nat)) =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 1) := by
  exact evalPanValueFfiClockProg_ite_true_some_progSize evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 (.const 5) (.annot "tag" "text") (.tick : Prog Nat)
    none none none 5 (.control (.normal (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi)) 1
    (by simp [evalPanValueExp]) (by decide)
    (by
      simpa only [progSize] using
        (evalPanValueFfiClockProg_annot_some evaluatorContext (fun _ _ => none)
          evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none) (fun _ => none)
          evaluatorFfi 1 "tag" "text" none none none))

/-- The same nonzero `Ite` at the call-aware budget; the branch is evaluated at
    the combined call-aware branch budget. -/
example : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
    [] [] 0 0 8 (progCallFuel 7 (.ite (.const 5) (.annot "tag" "text") (.tick : Prog Nat)))
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.ite (.const 5) (.annot "tag" "text") (.tick : Prog Nat)) =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 1) := by
  exact evalPanValueFfiClockProg_ite_true_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 (.const 5) (.annot "tag" "text") (.tick : Prog Nat)
    none none none 5 (.control (.normal (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi)) 1
    (by simp [evalPanValueExp]) (by decide)
    (by
      simpa only [progCallFuel] using
        (evalPanValueFfiClockProg_annot_some evaluatorContext (fun _ _ => none)
          evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none) (fun _ => none)
          evaluatorFfi 1 "tag" "text" none none none))

/-- `progSize`-indexed `Call` fuel adequacy: one structural step covers the node. -/
example (outcome : PanValueFfiClockOutcome Nat Unit) (nextClock : Nat)
    (hcall : evalPanValueFfiClockCall evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (progSize (.call none "f" ([] : List (Exp Nat))) - 1) (fun _ => none)
      (fun _ => none) (fun _ => none) evaluatorFfi 1 none "f" [] =
      some (outcome, nextClock)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8 (progSize (.call none "f" ([] : List (Exp Nat)))) (fun _ => none)
      (fun _ => none) (fun _ => none) evaluatorFfi 1 (.call none "f" ([] : List (Exp Nat))) none none none =
    some (outcome, nextClock) := by
  exact evalPanValueFfiClockProg_call_some_progSize evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 (fun _ => none) (fun _ => none) (fun _ => none)
    evaluatorFfi 1 none "f" [] outcome nextClock none none none hcall

/-- `progSize`-indexed returning `DecCall` fuel adequacy. -/
example
    (hcall : evalPanValueFfiClockCall evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 (progSize (.annot "tag" "text" : Prog Nat))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none "f" []
      (preserveReturnLocals := true) =
      some (.control (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi [.word 5]), 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progSize (.decCall "x" .one "f" [] (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.decCall "x" .one "f" [] (.annot "tag" "text")) none none none =
    some (panValueFfiClockRestoreLocal "x" none
      (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
        (fun _ => none) (fun _ => none) evaluatorFfi)), 1) := by
  exact evalPanValueFfiClockProg_decCall_returned_some_progSize evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "x" .one "f" [] (.annot "tag" "text")
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi (.word 5) 1
    (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
      (fun _ => none) (fun _ => none) evaluatorFfi)) 1 none none none hcall
    (by simp [panValueShape, panShapeMatches])
    (by
      simpa only [progSize] using
        (evalPanValueFfiClockProg_annot_some evaluatorContext (fun _ _ => none)
          evaluatorHandler [] [] 0 0 8 0
          (updatePanValueMap (fun _ => none) "x" (.word 5)) (fun _ => none)
          (fun _ => none) evaluatorFfi 1 "tag" "text" none none none))

/-- The returning `DecCall` at the call-aware budget. -/
example
    (hcall : evalPanValueFfiClockCall evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (max 7 (progCallFuel 7 (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none "f" []
      (preserveReturnLocals := true) =
      some (.control (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi [.word 5]), 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progCallFuel 7 (.decCall "x" .one "f" [] (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.decCall "x" .one "f" [] (.annot "tag" "text")) none none none =
    some (panValueFfiClockRestoreLocal "x" none
      (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
        (fun _ => none) (fun _ => none) evaluatorFfi)), 1) := by
  exact evalPanValueFfiClockProg_decCall_returned_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "x" .one "f" [] (.annot "tag" "text")
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi (.word 5) 1
    (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
      (fun _ => none) (fun _ => none) evaluatorFfi)) 1 none none none hcall
    (by simp [panValueShape, panShapeMatches])
    (by
      simpa [progCallFuel] using
        (evalPanValueFfiClockProg_annot_some evaluatorContext (fun _ _ => none)
          evaluatorHandler [] [] 0 0 8 6
          (updatePanValueMap (fun _ => none) "x" (.word 5)) (fun _ => none)
          (fun _ => none) evaluatorFfi 1 "tag" "text" none none none))

/-- The raising `DecCall` at the call-aware budget. -/
example
    (hcall : evalPanValueFfiClockCall evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (max 7 (progCallFuel 7 (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none "f" []
      (preserveReturnLocals := true) =
      some (.control (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi "E" (.word 5)), 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progCallFuel 7 (.decCall "x" .one "f" [] (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.decCall "x" .one "f" [] (.annot "tag" "text")) none none none =
    some (.control (.raised (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi "E" (.word 5)), 1) := by
  exact evalPanValueFfiClockProg_decCall_raised_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "x" .one "f" [] (.annot "tag" "text")
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi "E" (.word 5) 1
    none none none hcall

/-- The timing-out `DecCall` at the call-aware budget. -/
example
    (hcall : evalPanValueFfiClockCall evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (max 7 (progCallFuel 7 (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none "f" []
      (preserveReturnLocals := true) =
      some (.timeout (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi, 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progCallFuel 7 (.decCall "x" .one "f" [] (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.decCall "x" .one "f" [] (.annot "tag" "text")) none none none =
    some (.timeout (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi, 1) := by
  exact evalPanValueFfiClockProg_decCall_timeout_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "x" .one "f" [] (.annot "tag" "text")
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    none none none hcall

/-- The final-FFI `DecCall` at the call-aware budget. -/
example
    (event : FfiFinalEvent)
    (hcall : evalPanValueFfiClockCall evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (max 7 (progCallFuel 7 (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none "f" []
      (preserveReturnLocals := true) =
      some (.control (.finalFfi (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi event), 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progCallFuel 7 (.decCall "x" .one "f" [] (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.decCall "x" .one "f" [] (.annot "tag" "text")) none none none =
    some (.control (.finalFfi (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi event), 1) := by
  exact evalPanValueFfiClockProg_decCall_finalFfi_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "x" .one "f" [] (.annot "tag" "text")
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi event 1
    none none none hcall

/-- A structural normal program succeeds normally at its call-aware budget. -/
example :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progCallFuel 5 (.seq (.skip : Prog Nat) (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.seq (.skip : Prog Nat) (.annot "tag" "text")) none none none =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 1) := by
  exact evalPanValueFfiClockProg_normalProg_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 5
    (.seq (.skip : Prog Nat) (.annot "tag" "text")) (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 none none none
    (PanValueFfiClockNormalProg.seq (.skip : Prog Nat) (.annot "tag" "text")
      PanValueFfiClockNormalProg.skip (PanValueFfiClockNormalProg.annot "tag" "text"))

/-- The normal fragment is preserved by the `pan_simp` transform. -/
example :
    PanValueFfiClockNormalProg
      (panSimpProg (.seq (.skip : Prog Nat) (.annot "tag" "text"))) :=
  PanValueFfiClockNormalProg_panSimpProg
    (PanValueFfiClockNormalProg.seq (.skip : Prog Nat) (.annot "tag" "text")
      PanValueFfiClockNormalProg.skip (PanValueFfiClockNormalProg.annot "tag" "text"))

/-- The transformed normal fragment evaluates normally at its call-aware budget. -/
example
    (h : PanValueFfiClockNormalProg
      (.seq (.skip : Prog Nat) (.annot "tag" "text"))) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progCallFuel 5 (panSimpProg (.seq (.skip : Prog Nat) (.annot "tag" "text"))))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (panSimpProg (.seq (.skip : Prog Nat) (.annot "tag" "text"))) none none none =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 1) :=
  evalPanValueFfiClockProg_panSimpProg_normalProg_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 5
    (.seq (.skip : Prog Nat) (.annot "tag" "text")) (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 none none none h

/-- A call with a destination produces a `normal` result at the call-aware budget. -/
example
    (hfunctions : PanValueFfiClockFunctionsReturnSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8
      none none none)
    (hassign : ∀ (finalGlobals : VarName → Option (PanValue Nat)),
      ∃ (assignedLocals assignedGlobals : VarName → Option (PanValue Nat)),
        assignPanValueCallResult (fun _ => none) finalGlobals (some (VarKind.local, "x"))
          [.word 5] (structs := []) = some (assignedLocals, assignedGlobals))
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) (memoryAccess := none) = some ([] : List (PanValue Nat)))
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] ([] : List (PanValue Nat)) =
      some (fun _ => none))
    (hwithin : panValueValuesWithinLimit [] ([] : List (PanValue Nat)) = true) :
    ∃ (assignedLocals assignedGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progCallFuel 5 (.call (some ((VarKind.local, "x"), none)) "f" ([] : List (Exp Nat))))
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
        (.call (some ((VarKind.local, "x"), none)) "f" []) none none none =
      some (.control (.normal assignedLocals assignedGlobals finalMemory finalFfi),
        finalClock) :=
  evalPanValueFfiClockProg_call_destination_of_functions_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 5
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 "f" []
    (some (VarKind.local, "x")) [] (.skip : Prog Nat) [] (fun _ => none) none hfunctions
    (by simp [progSize]) hargs hlookup hbind (by decide) hwithin hassign

/-- A destination call composed with a normal continuation keeps the intermediate
state and clock at the sequence's call-aware budget. -/
example
    (hcall : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (progCallFuel 5 (.call (some ((VarKind.local, "x"), none)) "f"
        ([] : List (Exp Nat))))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.call (some ((VarKind.local, "x"), none)) "f" []) none none none =
      some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi), 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progCallFuel 5 (.seq (.call (some ((VarKind.local, "x"), none)) "f"
        ([] : List (Exp Nat))) (.skip : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.seq (.call (some ((VarKind.local, "x"), none)) "f" []) (.skip : Prog Nat))
      none none none =
      some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi), 1) :=
  evalPanValueFfiClockProg_seq_normal_of_first_normal_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 5
    (.call (some ((VarKind.local, "x"), none)) "f" ([] : List (Exp Nat)))
    (.skip : Prog Nat)
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none none none
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 hcall
    PanValueFfiClockNormalProg.skip

/-- Two destination calls compose at the sequence's call-aware budget, keeping the
second call's result and clock. -/
example
    (hcall₁ : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (progCallFuel 5 (.call (some ((VarKind.local, "x"), none)) "f"
        ([] : List (Exp Nat))))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.call (some ((VarKind.local, "x"), none)) "f" []) none none none =
      some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi), 1))
    (hcall₂ : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (progCallFuel 5 (.call (some ((VarKind.local, "y"), none)) "g"
        ([] : List (Exp Nat))))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.call (some ((VarKind.local, "y"), none)) "g" []) none none none =
      some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi), 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progCallFuel 5 (.seq (.call (some ((VarKind.local, "x"), none)) "f"
        ([] : List (Exp Nat))) (.call (some ((VarKind.local, "y"), none)) "g"
        ([] : List (Exp Nat)))))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.seq (.call (some ((VarKind.local, "x"), none)) "f" [])
        (.call (some ((VarKind.local, "y"), none)) "g" []))
      none none none =
      some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi), 1) :=
  evalPanValueFfiClockProg_seq_of_first_normal_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 5
    (.call (some ((VarKind.local, "x"), none)) "f" ([] : List (Exp Nat)))
    (.call (some ((VarKind.local, "y"), none)) "g" ([] : List (Exp Nat)))
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none none none
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi))
    1 hcall₁ hcall₂

/-- A destination call followed by a normal continuation composes at the
sequence's call-aware budget, keeping the assigned state and clock. -/
example
    (hfunctions : PanValueFfiClockFunctionsReturnSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8
      none none none)
    (hassign : ∀ (finalGlobals : VarName → Option (PanValue Nat)),
      ∃ (assignedLocals assignedGlobals : VarName → Option (PanValue Nat)),
        assignPanValueCallResult (fun _ => none) finalGlobals (some (VarKind.local, "x"))
          [.word 5] (structs := []) = some (assignedLocals, assignedGlobals))
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) (memoryAccess := none) = some ([] : List (PanValue Nat)))
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] ([] : List (PanValue Nat)) =
      some (fun _ => none))
    (hwithin : panValueValuesWithinLimit [] ([] : List (PanValue Nat)) = true) :
    ∃ (assignedLocals assignedGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progCallFuel 5
          (.seq (.call (some ((VarKind.local, "x"), none)) "f"
            ([] : List (Exp Nat))) (.skip : Prog Nat)))
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
        (.seq (.call (some ((VarKind.local, "x"), none)) "f" []) (.skip : Prog Nat))
        none none none =
      some (.control (.normal assignedLocals assignedGlobals finalMemory finalFfi),
        finalClock) :=
  evalPanValueFfiClockProg_seq_call_destination_normal_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 5
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 "f" []
    (some (VarKind.local, "x")) [] (.skip : Prog Nat) [] (fun _ => none)
    (.skip : Prog Nat) none hfunctions (by simp [progSize]) hargs hlookup hbind
    (by decide) hwithin hassign PanValueFfiClockNormalProg.skip

/-- A normal node followed by a destination call composes at the sequence's
call-aware budget, keeping the assigned state and clock. -/
example
    (hfunctions : PanValueFfiClockFunctionsReturnSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8
      none none none)
    (hassign : ∀ (finalGlobals : VarName → Option (PanValue Nat)),
      ∃ (assignedLocals assignedGlobals : VarName → Option (PanValue Nat)),
        assignPanValueCallResult (fun _ => none) finalGlobals (some (VarKind.local, "x"))
          [.word 5] (structs := []) = some (assignedLocals, assignedGlobals))
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) (memoryAccess := none) = some ([] : List (PanValue Nat)))
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] ([] : List (PanValue Nat)) =
      some (fun _ => none))
    (hwithin : panValueValuesWithinLimit [] ([] : List (PanValue Nat)) = true) :
    ∃ (assignedLocals assignedGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progCallFuel 5
          (.seq (.skip : Prog Nat)
            (.call (some ((VarKind.local, "x"), none)) "f"
              ([] : List (Exp Nat)))))
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
        (.seq (.skip : Prog Nat)
          (.call (some ((VarKind.local, "x"), none)) "f" []))
        none none none =
      some (.control (.normal assignedLocals assignedGlobals finalMemory finalFfi),
        finalClock) :=
  evalPanValueFfiClockProg_seq_normal_first_call_destination_progCallFuel
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))]
    0 0 8 5 (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.skip : Prog Nat) "f" [] (some (VarKind.local, "x")) [] (.skip : Prog Nat) []
    (fun _ => none) none PanValueFfiClockNormalProg.skip hfunctions
    (by simp [progSize]) hargs hlookup hbind (by decide) hwithin hassign

/-- A conditional whose branches lie in the normal fragment stays normal with the
state and clock unchanged. -/
example :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progCallFuel 5 (.ite (.const 5) (.annot "tag" "text") (.skip : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.ite (.const 5) (.annot "tag" "text") (.skip : Prog Nat))
      none none none =
      some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi), 1) :=
  evalPanValueFfiClockProg_ite_true_normal_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 5
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.const 5) (.annot "tag" "text") (.skip : Prog Nat) none none none 5
    (by simp [evalPanValueExp]) (by decide)
    (PanValueFfiClockNormalProg.annot "tag" "text")
    PanValueFfiClockNormalProg.skip

/-- The zero-condition branch of the same conditional also stays normal. -/
example :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progCallFuel 5 (.ite (.const 0) (.annot "tag" "text") (.skip : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.ite (.const 0) (.annot "tag" "text") (.skip : Prog Nat))
      none none none =
      some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi), 1) :=
  evalPanValueFfiClockProg_ite_false_normal_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 5
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.const 0) (.annot "tag" "text") (.skip : Prog Nat) none none none 0
    (by simp [evalPanValueExp]) (by decide)
    (PanValueFfiClockNormalProg.annot "tag" "text")
    PanValueFfiClockNormalProg.skip

/-- Normal adequacy composes through sequences and conditionals: the normal
    fragment is normal-adequate, and so is a conditional over it. -/
example :
    PanValueFfiClockNormalAdequateProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 5 none none none
      (.ite (.const 5)
        (.seq (.skip : Prog Nat) (.annot "tag" "text"))
        (.skip : Prog Nat)) :=
  PanValueFfiClockNormalAdequateProg_ite evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 5 none none none (.const 5)
    (.seq (.skip : Prog Nat) (.annot "tag" "text")) (.skip : Prog Nat)
    (fun _ _ _ => ⟨5, by simp [evalPanValueExp]⟩)
    (PanValueFfiClockNormalAdequateProg_seq evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 5 none none none (.skip : Prog Nat)
      (.annot "tag" "text")
      (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
        (fun _ _ => none) evaluatorHandler [] [] 0 0 8 5 none none none
        (.skip : Prog Nat) PanValueFfiClockNormalProg.skip)
      (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
        (fun _ _ => none) evaluatorHandler [] [] 0 0 8 5 none none none
        (.annot "tag" "text") (PanValueFfiClockNormalProg.annot "tag" "text")))
    (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 5 none none none
      (.skip : Prog Nat) PanValueFfiClockNormalProg.skip)

/-- A zero-condition `While` is normal-adequate at the call-aware budget. -/
example :
    PanValueFfiClockNormalAdequateProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 5 none none none
      (.while (.const 0) (.skip : Prog Nat)) :=
  PanValueFfiClockNormalAdequateProg_while_zero evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 5 none none none (.const 0) (.skip : Prog Nat)
    (fun _ _ _ => ⟨0, by simp [evalPanValueExp], by decide⟩)

/-! A declaration with a shape-matching constant and a normal-adequate body. -/
example :
    PanValueFfiClockNormalAdequateProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 5 none none none
      (.dec "x" .one (.const 5) (.skip : Prog Nat)) :=
  PanValueFfiClockNormalAdequateProg_dec evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 5 none none none "x" .one (.const 5)
    (.skip : Prog Nat)
    (fun _ _ _ =>
      ⟨.word 5, by simp [evalPanValueExp], by simp [panValueShape, panShapeMatches]⟩)
    (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 5 none none none
      (.skip : Prog Nat) PanValueFfiClockNormalProg.skip)

/-- A memory-store leaf is normal-adequate via the generic leaf constructor. -/
example :
    PanValueFfiClockNormalAdequateProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 5 none none none
      (.store (.const 7) (.const 9)) :=
  PanValueFfiClockNormalAdequateProg_leaf evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 5 none none none (.store (.const 7) (.const 9))
    (PanValueFfiLeafProg.store (.const 7) (.const 9))
    (by
      intro locals globals memory ffi
      exact ⟨locals, globals, updatePanValueMemory memory 7 (.word 9), ffi, 3, by
        simp [evalPanValueFfiProgSteps, panValueStoreResult, evalPanValueExpCounted,
          evalPanValueExp, panValueExpStepCost, panValueStoreWithAccess,
          panValueFlatStoreWords, panValueFlatWords, panValueFlatWordsFuel,
          panValueFlatOffset, updatePanValueMemory]⟩)

/-- A destination call is normal-adequate from a nonzero clock, given the
per-state argument/shape evidence and the destination assignment. -/
example
    (hfunctions : PanValueFfiClockFunctionsReturnSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8
      none none none)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hargs : ∀ (locals globals : VarName → Option (PanValue Nat))
      (memory : Nat → Option (PanValue Nat)),
      ∃ (values : List (PanValue Nat)) (calleeLocals : VarName → Option (PanValue Nat)),
        evalPanValueExps [] locals globals memory 0 0 8 ([] : List (Exp Nat))
          (memoryAccess := none) = some values ∧
        bindPanValueParameters [] values = some calleeLocals ∧
        panValueValuesWithinLimit [] values = true)
    (hassign : ∀ (locals : VarName → Option (PanValue Nat))
      (finalGlobals : VarName → Option (PanValue Nat)) (values : List (PanValue Nat)),
      ∃ (assignedLocals assignedGlobals : VarName → Option (PanValue Nat)),
        assignPanValueCallResult locals finalGlobals (some (VarKind.local, "x")) values
          (structs := []) = some (assignedLocals, assignedGlobals)) :
    PanValueFfiClockNormalAdequateProgAt 5 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 5 none none none
      (.call (some ((VarKind.local, "x"), none)) "f" []) :=
  PanValueFfiClockNormalAdequateProgAt_call_destination 5 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 5
    none "f" [] (some (VarKind.local, "x")) [] (.skip : Prog Nat) hfunctions
    (by simp [progSize]) hlookup (by decide) hargs hassign

/-- A caught-handler call is normal-adequate from a nonzero clock, given the
per-state argument evidence, the handler validity, and the caught exception. -/
example
    (hfunctions : PanValueFfiClockFunctionsRaiseAsSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8
      none none none "E")
    (hhandler : PanValueFfiClockHandlerNormalSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8
      none none none)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hargs : ∀ (locals globals : VarName → Option (PanValue Nat))
      (memory : Nat → Option (PanValue Nat)),
      ∃ (values : List (PanValue Nat)) (calleeLocals : VarName → Option (PanValue Nat)),
        evalPanValueExps [] locals globals memory 0 0 8 ([] : List (Exp Nat))
          (memoryAccess := none) = some values ∧
        bindPanValueParameters [] values = some calleeLocals ∧
        panValueParametersValid [] none "f" values = true)
    (hhandlerValid : ∀ (locals : VarName → Option (PanValue Nat)) (value : PanValue Nat),
      panValueExceptionValid [] none "E" value = true →
      panValuePayloadWithinLimit [] value = true →
      panValueHandlerValid [] none locals "x" value = true) :
    PanValueFfiClockNormalAdequateProgAt 5 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 7 none none none
      (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" []) :=
  PanValueFfiClockNormalAdequateProgAt_call_caught_handler 5 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 7
    none none none "f" [] [] (.skip : Prog Nat) "E" "E" "x" (.skip : Prog Nat)
    hfunctions hhandler (by simp [progSize]) hlookup (by decide) hargs rfl hhandlerValid

/-- A clock-indexed node (such as a call) can be followed by any clock-free
normal continuation. -/
example
    (hfirst : PanValueFfiClockNormalAdequateProgAt 5 evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 5
      none none none (.call (some ((VarKind.local, "x"), none)) "f" [])) :
    PanValueFfiClockNormalAdequateProgAt 5 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 5 none none none
      (.seq (.call (some ((VarKind.local, "x"), none)) "f" []) (.skip : Prog Nat)) :=
  PanValueFfiClockNormalAdequateProgAt_seq_of_adequate 5 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 5
    none none none (.call (some ((VarKind.local, "x"), none)) "f" []) (.skip : Prog Nat)
    hfirst (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 5
      none none none (.skip : Prog Nat) PanValueFfiClockNormalProg.skip)

/-- A returning decCall node with a singleton call result is clock-indexed
normal-adequate. -/
example
    (hcall : ∀ (locals globals : VarName → Option (PanValue Nat))
      (memory : Nat → Option (PanValue Nat)) (ffi : FfiState Unit),
      ∃ (nextLocals nextGlobals : VarName → Option (PanValue Nat))
        (nextMemory : Nat → Option (PanValue Nat)) (nextFfi : FfiState Unit)
        (value : PanValue Nat) (callClock : Nat),
        evalPanValueFfiClockCall evaluatorContext (fun _ _ => none) evaluatorHandler [] []
          0 0 8 (max 7 (progCallFuel 7 (.skip : Prog Nat))) locals globals memory ffi 5
          none "f" [] (memoryAccess := none) (contracts := none) (memoryHandler := none)
          (preserveReturnLocals := true) =
          some (.control (.returned nextLocals nextGlobals nextMemory nextFfi [value]),
            callClock))
    (hmatch : ∀ value : PanValue Nat,
      panShapeMatches (panValueShape [] value) .one = true) :
    PanValueFfiClockNormalAdequateProgAt 5 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 7 none none none
      (.decCall "x" .one "f" [] (.skip : Prog Nat)) :=
  PanValueFfiClockNormalAdequateProgAt_decCall_returned 5 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none "x" .one "f" []
    (.skip : Prog Nat) hcall hmatch
    (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.skip : Prog Nat) PanValueFfiClockNormalProg.skip)

/-- A clock-indexed conditional composes a clock-indexed branch (e.g. a call)
    with a clock-free branch. -/
example
    (hthen : PanValueFfiClockNormalAdequateProgAt 5 evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.call (some ((VarKind.local, "x"), none)) "f" [])) :
    PanValueFfiClockNormalAdequateProgAt 5 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 7 none none none
      (.ite (.const 5) (.call (some ((VarKind.local, "x"), none)) "f" [])
        (.skip : Prog Nat)) :=
  PanValueFfiClockNormalAdequateProgAt_ite 5 evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 7 none none none (.const 5)
    (.call (some ((VarKind.local, "x"), none)) "f" []) (.skip : Prog Nat)
    (fun _ _ _ => ⟨5, by simp [evalPanValueExp]⟩) hthen
    (PanValueFfiClockNormalAdequateProgAt_of_adequate evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.skip : Prog Nat) 5
      (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
        (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
        (.skip : Prog Nat) PanValueFfiClockNormalProg.skip))

/-- A tick is normal-adequate from a nonzero clock, with the clock decremented. -/
example :
    PanValueFfiClockNormalAdequateProgAt 5 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 7 none none none (.tick : Prog Nat) :=
  PanValueFfiClockNormalAdequateProgAt_tick 5 evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 7 none none none (by decide)

/-- Clock-bounded adequacy sequences two clock-free programs. -/
example :
    PanValueFfiClockNormalAdequateProgUpTo 5 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 7 none none none
      (.seq (.skip : Prog Nat) (.annot "tag" "text")) :=
  PanValueFfiClockNormalAdequateProgUpTo_seq 5 evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 7 none none none (.skip : Prog Nat)
    (.annot "tag" "text")
    (PanValueFfiClockNormalAdequateProgUpTo_of_adequate 5 evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.skip : Prog Nat)
      (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
        (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
        (.skip : Prog Nat) PanValueFfiClockNormalProg.skip))
    (PanValueFfiClockNormalAdequateProgUpTo_of_adequate 5 evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.annot "tag" "text")
      (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
        (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
        (.annot "tag" "text") (.annot "tag" "text")))

/-- Lower-bounded adequacy also accepts clock-free programs. -/
example :
    PanValueFfiClockNormalAdequateProgFrom 5 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 7 none none none
      (.annot "tag" "text") :=
  PanValueFfiClockNormalAdequateProgFrom_of_adequate 5 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.annot "tag" "text")
    (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.annot "tag" "text") (.annot "tag" "text"))

/-- A destination call is lower-bounded adequate from one, and sequences with a
    clock-free continuation. -/
example
    (hfunctions : PanValueFfiClockFunctionsReturnSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))]
      0 0 8 none none none)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hargs : ∀ (locals globals : VarName → Option (PanValue Nat))
      (memory : Nat → Option (PanValue Nat)),
      ∃ (values : List (PanValue Nat)) (calleeLocals : VarName → Option (PanValue Nat)),
        evalPanValueExps [] locals globals memory 0 0 8 ([] : List (Exp Nat))
          (memoryAccess := none) = some values ∧
        bindPanValueParameters [] values = some calleeLocals ∧
        panValueValuesWithinLimit [] values = true)
    (hassign : ∀ (locals : VarName → Option (PanValue Nat))
      (finalGlobals : VarName → Option (PanValue Nat)) (values : List (PanValue Nat)),
      ∃ (assignedLocals assignedGlobals : VarName → Option (PanValue Nat)),
        assignPanValueCallResult locals finalGlobals
          (some (VarKind.local, "x")) values (structs := []) =
          some (assignedLocals, assignedGlobals)) :
    PanValueFfiClockNormalAdequateProgFrom 1 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 5 none none none
      (.seq (.call (some ((VarKind.local, "x"), none)) "f" [])
        (.annot "tag" "text")) :=
  PanValueFfiClockNormalAdequateProgFrom_seq_adequate 1 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))]
    0 0 8 5 none none none
    (.call (some ((VarKind.local, "x"), none)) "f" []) (.annot "tag" "text")
    (PanValueFfiClockNormalAdequateProgFrom_call_destination 1 (by decide)
      evaluatorContext (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 5 none "f" []
      (some (VarKind.local, "x")) [] (.skip : Prog Nat) hfunctions
      (by simp [progSize]) hlookup hargs hassign)
    (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))]
      0 0 8 5 none none none (.annot "tag" "text") (.annot "tag" "text"))

/-- A caught-handler call is lower-bounded adequate from one, with explicit
    raise and handler success evidence for the generic function table. -/
example
    (hfunctions : PanValueFfiClockFunctionsRaiseAsSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))]
      0 0 8 none none none "E")
    (hhandler : PanValueFfiClockHandlerNormalSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))]
      0 0 8 none none none)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hargs : ∀ (locals globals : VarName → Option (PanValue Nat))
      (memory : Nat → Option (PanValue Nat)),
      ∃ (values : List (PanValue Nat)) (calleeLocals : VarName → Option (PanValue Nat)),
        evalPanValueExps [] locals globals memory 0 0 8 ([] : List (Exp Nat))
          (memoryAccess := none) = some values ∧
        bindPanValueParameters [] values = some calleeLocals ∧
        panValueParametersValid [] none "f" values = true)
    (hhandlerValid : ∀ (locals : VarName → Option (PanValue Nat))
      (value : PanValue Nat),
      panValueExceptionValid [] none "E" value = true →
      panValuePayloadWithinLimit [] value = true →
      panValueHandlerValid [] none locals "x" value = true) :
    PanValueFfiClockNormalAdequateProgFrom 1 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 7 none none none
      (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" []) :=
  PanValueFfiClockNormalAdequateProgFrom_call_caught_handler 1 (by decide)
    evaluatorContext (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 7 none none none "f" [] []
    (.skip : Prog Nat) "E" "E" "x" (.skip : Prog Nat) hfunctions hhandler
    (by simp [progSize]) hlookup rfl hargs hhandlerValid

/-- The lower-bounded fragment also covers declarations, conditionals and ticks
    (in addition to calls and sequences). -/
example :
    PanValueFfiClockNormalAdequateProgFrom 1 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 7 none none none
      (.dec "x" .one (.const 5) (.skip : Prog Nat)) :=
  PanValueFfiClockNormalAdequateProgFrom_dec 1 evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 7 none none none "x" .one (.const 5)
    (.skip : Prog Nat)
    (fun _ _ _ => ⟨.word 5, by simp [evalPanValueExp],
      by simp [panValueShape, panShapeMatches]⟩)
    (PanValueFfiClockNormalAdequateProgFrom_of_adequate 1 evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.skip : Prog Nat)
      (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
        (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
        (.skip : Prog Nat) PanValueFfiClockNormalProg.skip))

example :
    PanValueFfiClockNormalAdequateProgFrom 1 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 7 none none none
      (.ite (.const 5) (.skip : Prog Nat) (.skip : Prog Nat)) :=
  PanValueFfiClockNormalAdequateProgFrom_ite 1 evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 7 none none none (.const 5) (.skip : Prog Nat)
    (.skip : Prog Nat) (fun _ _ _ => ⟨5, by simp [evalPanValueExp]⟩)
    (PanValueFfiClockNormalAdequateProgFrom_of_adequate 1 evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.skip : Prog Nat)
      (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
        (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
        (.skip : Prog Nat) PanValueFfiClockNormalProg.skip))
    (PanValueFfiClockNormalAdequateProgFrom_of_adequate 1 evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.skip : Prog Nat)
      (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
        (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
        (.skip : Prog Nat) PanValueFfiClockNormalProg.skip))

example :
    PanValueFfiClockNormalAdequateProgFrom 1 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 7 none none none (.tick : Prog Nat) :=
  PanValueFfiClockNormalAdequateProgFrom_tick 1 (by decide) evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none

example :
    PanValueFfiClockNormalAdequateProgFrom 0 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 7 none none none
      (.while (.const 0) (.skip : Prog Nat)) :=
  PanValueFfiClockNormalAdequateProgFrom_while_zero 0 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.const 0) (.skip : Prog Nat) (fun _ _ _ => ⟨0, by simp [evalPanValueExp], by decide⟩)

/-- A returning declaration call is lower-bounded normal-adequate when the
    caller supplies the call result and the body is all-clock adequate. -/
example
    (hcall : ∀ (clock : Nat), 1 ≤ clock →
      ∀ (locals globals : VarName → Option (PanValue Nat))
        (memory : Nat → Option (PanValue Nat)) (ffi : FfiState Unit),
      ∃ (nextLocals nextGlobals : VarName → Option (PanValue Nat))
        (nextMemory : Nat → Option (PanValue Nat)) (nextFfi : FfiState Unit)
        (value : PanValue Nat) (callClock : Nat),
        evalPanValueFfiClockCall evaluatorContext (fun _ _ => none) evaluatorHandler
          [] [] 0 0 8 (max 7 (progCallFuel 7 (.skip : Prog Nat))) locals globals memory
          ffi clock none "f" [] (preserveReturnLocals := true) =
          some (.control (.returned nextLocals nextGlobals nextMemory nextFfi [value]),
            callClock))
    (hmatch : ∀ value : PanValue Nat,
      panShapeMatches (panValueShape [] value) .one = true) :
    PanValueFfiClockNormalAdequateProgFrom 1 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 7 none none none
      (.decCall "x" .one "f" [] (.skip : Prog Nat)) :=
  PanValueFfiClockNormalAdequateProgFrom_decCall_returned 1 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    "x" .one "f" [] (.skip : Prog Nat) hcall hmatch
    (evalPanValueFfiClockProg_normalAdequate_of_normalProg evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.skip : Prog Nat) PanValueFfiClockNormalProg.skip)

/-- A memory-store leaf is lower-bounded normal-adequate at any bound. -/
example :
    PanValueFfiClockNormalAdequateProgFrom 0 evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 5 none none none
      (.store (.const 7) (.const 9)) :=
  PanValueFfiClockNormalAdequateProgFrom_leaf 0 evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 5 none none none (.store (.const 7) (.const 9))
    (PanValueFfiLeafProg.store (.const 7) (.const 9))
    (by
      intro locals globals memory ffi
      exact ⟨locals, globals, updatePanValueMemory memory 7 (.word 9), ffi, 3, by
        simp [evalPanValueFfiProgSteps, panValueStoreResult, evalPanValueExpCounted,
          evalPanValueExp, panValueExpStepCost, panValueStoreWithAccess,
          panValueFlatStoreWords, panValueFlatWords, panValueFlatWordsFuel,
          panValueFlatOffset, updatePanValueMemory]⟩)

/-- The raised `DecCall` outcome also lifts to the declaration's progSize. -/
example
    (hcall : evalPanValueFfiClockCall evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 (progSize (.annot "tag" "text" : Prog Nat))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none "f" []
      (preserveReturnLocals := true) =
      some (.control (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi "E" (.word 5)), 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progSize (.decCall "x" .one "f" [] (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.decCall "x" .one "f" [] (.annot "tag" "text")) none none none =
    some (.control (.raised (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi "E" (.word 5)), 1) := by
  exact evalPanValueFfiClockProg_decCall_raised_some_progSize evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "x" .one "f" [] (.annot "tag" "text")
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi "E" (.word 5) 1
    none none none hcall

/-- A timed-out `DecCall` outcome lifts to the declaration's progSize. -/
example
    (hcall : evalPanValueFfiClockCall evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 (progSize (.annot "tag" "text" : Prog Nat))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none "f" []
      (preserveReturnLocals := true) =
      some (.timeout (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi, 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progSize (.decCall "x" .one "f" [] (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.decCall "x" .one "f" [] (.annot "tag" "text")) none none none =
    some (.timeout (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi, 1) := by
  exact evalPanValueFfiClockProg_decCall_timeout_some_progSize evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "x" .one "f" [] (.annot "tag" "text")
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none none none hcall

/-- A FinalFFI `DecCall` outcome lifts to the declaration's progSize. -/
example (event : FfiFinalEvent)
    (hcall : evalPanValueFfiClockCall evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 (progSize (.annot "tag" "text" : Prog Nat))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 none "f" []
      (preserveReturnLocals := true) =
      some (.control (.finalFfi (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi event), 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8
      (progSize (.decCall "x" .one "f" [] (.annot "tag" "text" : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.decCall "x" .one "f" [] (.annot "tag" "text")) none none none =
    some (.control (.finalFfi (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi event), 1) := by
  exact evalPanValueFfiClockProg_decCall_finalFfi_some_progSize evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "x" .one "f" [] (.annot "tag" "text")
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi event 1
    none none none hcall

/-- The general forall-functions call-adequacy theorem: a destination-free call
    into a single-entry table is discharged from an explicit hypothesis that
    every listed body returns at its own `progSize` budget. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsReturnSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true)
    (hwithin : panValueValuesWithinLimit [] values = true) :
    ∃ (finalGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progSize (.skip : Prog Nat) + 2) (fun _ => none) (fun _ => none)
        (fun _ => none) evaluatorFfi 1 (.call none "f" []) none none none =
      some (.control (.returned (fun _ => none) finalGlobals finalMemory finalFfi values),
        finalClock) := by
  exact evalPanValueFfiClockProg_call_none_of_functions evaluatorContext
    (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "f" [] [] (.skip : Prog Nat) values calleeLocals
    none none none hfunctions hargs hlookup hbind (by decide) hparams hwithin

/-- The call-aware budget form of the forall-functions call adequacy: with
    `callBudget = 7` (dominating `progSize body + 1 = 2`) the same call returns at
    `progCallFuel 7`. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsReturnSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true)
    (hwithin : panValueValuesWithinLimit [] values = true) :
    ∃ (finalGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progCallFuel 7 (.call none "f" ([] : List (Exp Nat)))) (fun _ => none) (fun _ => none)
        (fun _ => none) evaluatorFfi 1 (.call none "f" []) none none none =
      some (.control (.returned (fun _ => none) finalGlobals finalMemory finalFfi values),
        finalClock) := by
  exact evalPanValueFfiClockProg_call_none_of_functions_progCallFuel (α := Nat) (σ := Unit)
    evaluatorContext
    (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 7 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "f" ([] : List (Exp Nat)) [] (.skip : Prog Nat) values calleeLocals
    none none none hfunctions (by simp [progSize]) hargs hlookup hbind (by decide) hparams
    hwithin

/-- The general forall-functions timeout adequacy theorem, instantiated on a
    destination-free call into a single-entry table. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsTimeoutSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true) :
    ∃ (finalGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progSize (.skip : Prog Nat) + 2) (fun _ => none) (fun _ => none)
        (fun _ => none) evaluatorFfi 1 (.call none "f" []) none none none =
      some (.timeout (fun _ => none) finalGlobals finalMemory finalFfi, finalClock) := by
  exact evalPanValueFfiClockProg_call_timeout_of_functions evaluatorContext
    (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "f" [] [] (.skip : Prog Nat) values calleeLocals
    none none none hfunctions hargs hlookup hbind (by decide) hparams

/-- The general forall-functions uncaught-raise adequacy theorem, instantiated
    on a destination-free call into a single-entry table. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsRaiseSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true) :
    ∃ (exception : ExceptionId) (value : PanValue Nat)
      (finalGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progSize (.skip : Prog Nat) + 2) (fun _ => none) (fun _ => none)
        (fun _ => none) evaluatorFfi 1 (.call none "f" []) none none none =
      some (.control (.raised (fun _ => none) finalGlobals finalMemory finalFfi exception
        value), finalClock) := by
  exact evalPanValueFfiClockProg_call_raised_no_handler_of_functions evaluatorContext
    (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "f" [] [] (.skip : Prog Nat) values calleeLocals
    none none none hfunctions hargs hlookup hbind (by decide) hparams

/-- The general forall-functions terminal-FFI adequacy theorem, instantiated on a
    destination-free call into a single-entry table. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsFinalFfiSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true) :
    ∃ (finalGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (event : FfiFinalEvent) (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progSize (.skip : Prog Nat) + 2) (fun _ => none) (fun _ => none)
        (fun _ => none) evaluatorFfi 1 (.call none "f" []) none none none =
      some (.control (.finalFfi (fun _ => none) finalGlobals finalMemory finalFfi event),
        finalClock) := by
  exact evalPanValueFfiClockProg_call_finalFfi_of_functions evaluatorContext
    (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "f" [] [] (.skip : Prog Nat) values calleeLocals
    none none none hfunctions hargs hlookup hbind (by decide) hparams

/-- The general caught-handler adequacy theorem, instantiated on a call whose
    callee raises the caught exception and whose handler body is adequate. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsRaiseAsSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none "E")
    (hhandler : PanValueFfiClockHandlerSucceed evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true)
    (hhandlerValid : ∀ (value : PanValue Nat),
      panValueExceptionValid [] none "E" value = true →
      panValuePayloadWithinLimit [] value = true →
      panValueHandlerValid [] none (fun _ => none) "x" value = true) :
    ∃ (outcome : PanValueFfiClockOutcome Nat Unit) (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (max (progSize (.skip : Prog Nat)) (progSize (.skip : Prog Nat)) + 2)
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
        (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" []) none none none =
      some (outcome, finalClock) := by
  exact evalPanValueFfiClockProg_call_caught_handler_of_functions evaluatorContext
    (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "f" [] [] (.skip : Prog Nat) values calleeLocals
    "E" "E" "x" (.skip : Prog Nat) none none none hfunctions hhandler hargs hlookup
    hbind (by decide) hparams rfl hhandlerValid

/-- A caught-handler call whose handler returns `normal` yields that normal
    result at the call's combined budget. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsRaiseAsSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none "E")
    (hhandler : PanValueFfiClockHandlerNormalSucceed evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true)
    (hhandlerValid : ∀ (value : PanValue Nat),
      panValueExceptionValid [] none "E" value = true →
      panValuePayloadWithinLimit [] value = true →
      panValueHandlerValid [] none (fun _ => none) "x" value = true) :
    ∃ (finalLocals finalGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (max (progSize (.skip : Prog Nat)) (progSize (.skip : Prog Nat)) + 2)
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
        (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" []) none none none =
      some (.control (.normal finalLocals finalGlobals finalMemory finalFfi),
        finalClock) := by
  exact evalPanValueFfiClockProg_call_caught_handler_normal_of_functions
    evaluatorContext (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "f" [] [] (.skip : Prog Nat) values calleeLocals
    "E" "E" "x" (.skip : Prog Nat) none none none hfunctions hhandler hargs hlookup
    hbind (by decide) hparams rfl hhandlerValid

/-- The normal-handler caught-call adequacy at the call-aware budget. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsRaiseAsSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none "E")
    (hhandler : PanValueFfiClockHandlerNormalSucceed evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true)
    (hhandlerValid : ∀ (value : PanValue Nat),
      panValueExceptionValid [] none "E" value = true →
      panValuePayloadWithinLimit [] value = true →
      panValueHandlerValid [] none (fun _ => none) "x" value = true) :
    ∃ (finalLocals finalGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progCallFuel 7 (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" []))
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
        (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" []) none none none =
      some (.control (.normal finalLocals finalGlobals finalMemory finalFfi),
        finalClock) := by
  exact evalPanValueFfiClockProg_call_caught_handler_normal_of_functions_progCallFuel
    evaluatorContext (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 7 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "f" [] [] (.skip : Prog Nat) values calleeLocals
    "E" "E" "x" (.skip : Prog Nat) none none none hfunctions hhandler
    (by simp [progSize]) hargs hlookup hbind (by decide) hparams rfl hhandlerValid

/-- A normal node followed by a caught-handler call composes at the sequence's
    call-aware budget, keeping the handler's final state and clock. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsRaiseAsSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none "E")
    (hhandler : PanValueFfiClockHandlerNormalSucceed evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true)
    (hhandlerValid : ∀ (value : PanValue Nat),
      panValueExceptionValid [] none "E" value = true →
      panValuePayloadWithinLimit [] value = true →
      panValueHandlerValid [] none (fun _ => none) "x" value = true) :
    ∃ (finalLocals finalGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progCallFuel 7
          (.seq (.skip : Prog Nat)
            (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" [])))
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
        (.seq (.skip : Prog Nat)
          (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" []))
        none none none =
      some (.control (.normal finalLocals finalGlobals finalMemory finalFfi),
        finalClock) := by
  exact evalPanValueFfiClockProg_seq_normal_first_call_caught_handler_progCallFuel
    evaluatorContext (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 7 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 (.skip : Prog Nat) "f" [] [] (.skip : Prog Nat)
    values calleeLocals "E" "E" "x" (.skip : Prog Nat) none none none
    PanValueFfiClockNormalProg.skip hfunctions hhandler (by simp [progSize]) hargs
    hlookup hbind (by decide) hparams rfl hhandlerValid

/-- A caught-handler call followed by an arbitrary continuation composes once
    the caller supplies the continuation's evaluation from the returned state. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsRaiseAsSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none "E")
    (hhandler : PanValueFfiClockHandlerNormalSucceed evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true)
    (hhandlerValid : ∀ (value : PanValue Nat),
      panValueExceptionValid [] none "E" value = true →
      panValuePayloadWithinLimit [] value = true →
      panValueHandlerValid [] none (fun _ => none) "x" value = true) :
    ∃ (result : PanValueFfiClockOutcome Nat Unit) (resultClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progCallFuel 7
          (.seq
            (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" [])
            (.skip : Prog Nat)))
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
        (.seq
          (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" [])
          (.skip : Prog Nat))
        none none none =
      some (result, resultClock) := by
  exact evalPanValueFfiClockProg_seq_call_caught_handler_continuation_progCallFuel
    evaluatorContext (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 7 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "f" [] [] (.skip : Prog Nat) values calleeLocals
    "E" "E" "x" (.skip : Prog Nat) (.skip : Prog Nat) none none none hfunctions
    hhandler (by simp [progSize]) hargs hlookup hbind (by decide) hparams rfl
    hhandlerValid
    (fun midLocals midGlobals midMemory midFfi midClock =>
      ⟨_, _, evalPanValueFfiClockProg_normalProg_some_progCallFuel evaluatorContext
        (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8
        7 (.skip : Prog Nat) midLocals midGlobals midMemory midFfi midClock none none
        none PanValueFfiClockNormalProg.skip⟩)

/-- A destination call followed by an arbitrary continuation composes once the
    caller supplies the continuation's evaluation from the assigned state. -/
example
    (hfunctions : PanValueFfiClockFunctionsReturnSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8
      none none none)
    (hassign : ∀ (finalGlobals : VarName → Option (PanValue Nat)),
      ∃ (assignedLocals assignedGlobals : VarName → Option (PanValue Nat)),
        assignPanValueCallResult (fun _ => none) finalGlobals (some (VarKind.local, "x"))
          [.word 5] (structs := []) = some (assignedLocals, assignedGlobals))
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) (memoryAccess := none) = some ([] : List (PanValue Nat)))
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] ([] : List (PanValue Nat)) =
      some (fun _ => none))
    (hwithin : panValueValuesWithinLimit [] ([] : List (PanValue Nat)) = true) :
    ∃ (result : PanValueFfiClockOutcome Nat Unit) (resultClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progCallFuel 5
          (.seq (.call (some ((VarKind.local, "x"), none)) "f"
            ([] : List (Exp Nat))) (.skip : Prog Nat)))
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
        (.seq (.call (some ((VarKind.local, "x"), none)) "f" []) (.skip : Prog Nat))
        none none none =
      some (result, resultClock) :=
  evalPanValueFfiClockProg_seq_call_destination_continuation_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 5
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1 "f" []
    (some (VarKind.local, "x")) [] (.skip : Prog Nat) [] (fun _ => none)
    (.skip : Prog Nat) none hfunctions (by simp [progSize]) hargs hlookup hbind
    (by decide) hwithin hassign
    (fun midLocals midGlobals midMemory midFfi midClock =>
      ⟨_, _, evalPanValueFfiClockProg_normalProg_some_progCallFuel evaluatorContext
        (fun _ _ => none) evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8
        5 (.skip : Prog Nat) midLocals midGlobals midMemory midFfi midClock none none
        none PanValueFfiClockNormalProg.skip⟩)

/-- The caught-handler call adequacy at the call-aware budget. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsRaiseAsSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none "E")
    (hhandler : PanValueFfiClockHandlerSucceed evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true)
    (hhandlerValid : ∀ (value : PanValue Nat),
      panValueExceptionValid [] none "E" value = true →
      panValuePayloadWithinLimit [] value = true →
      panValueHandlerValid [] none (fun _ => none) "x" value = true) :
    ∃ (outcome : PanValueFfiClockOutcome Nat Unit) (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progCallFuel 7 (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" []))
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
        (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" []) none none none =
      some (outcome, finalClock) := by
  exact evalPanValueFfiClockProg_call_caught_handler_of_functions_progCallFuel
    evaluatorContext (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 7 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "f" [] [] (.skip : Prog Nat) values calleeLocals
    "E" "E" "x" (.skip : Prog Nat) none none none hfunctions hhandler
    (by simp [progSize]) hargs hlookup hbind (by decide) hparams rfl hhandlerValid

/-- A caught-handler call whose handler returns `normal` at the call-aware budget. -/
example (values : List (PanValue Nat))
    (calleeLocals : VarName → Option (PanValue Nat))
    (hfunctions : PanValueFfiClockFunctionsRaiseAsSucceed evaluatorContext
      (fun _ _ => none) evaluatorHandler []
      [("f", [], (.skip : Prog Nat))] 0 0 8 none none none "E")
    (hhandler : PanValueFfiClockHandlerNormalSucceed evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [("f", [], (.skip : Prog Nat))] 0 0 8 none none none)
    (hargs : evalPanValueExps [] (fun _ => none) (fun _ => none) (fun _ => none) 0 0 8
      ([] : List (Exp Nat)) = some values)
    (hlookup : lookupPanFunction "f" [("f", [], (.skip : Prog Nat))] =
      some ([], (.skip : Prog Nat)))
    (hbind : bindPanValueParameters [] values = some calleeLocals)
    (hparams : panValueParametersValid [] none "f" values = true)
    (hhandlerValid : ∀ (value : PanValue Nat),
      panValueExceptionValid [] none "E" value = true →
      panValuePayloadWithinLimit [] value = true →
      panValueHandlerValid [] none (fun _ => none) "x" value = true) :
    ∃ (finalLocals finalGlobals : VarName → Option (PanValue Nat))
      (finalMemory : Nat → Option (PanValue Nat)) (finalFfi : FfiState Unit)
      (finalClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
        [] [("f", [], (.skip : Prog Nat))] 0 0 8
        (progCallFuel 7 (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" []))
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
        (.call (some (none, some ("E", "x", (.skip : Prog Nat)))) "f" []) none none none =
      some (.control (.normal finalLocals finalGlobals finalMemory finalFfi), finalClock) := by
  exact evalPanValueFfiClockProg_call_caught_handler_normal_of_functions_progCallFuel
    evaluatorContext (fun _ _ => none) evaluatorHandler []
    [("f", [], (.skip : Prog Nat))] 0 0 8 7 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "f" [] [] (.skip : Prog Nat) values calleeLocals
    "E" "E" "x" (.skip : Prog Nat) none none none hfunctions hhandler
    (by simp [progSize]) hargs hlookup hbind (by decide) hparams rfl hhandlerValid

/-- Lifting a successful `Call` outcome through the clocked evaluator. -/
example (outcome : PanValueFfiClockOutcome Nat Unit) (nextClock : Nat)
    (hcall : evalPanValueFfiClockCall evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 none "f" [] = some (outcome, nextClock)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8 2 (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.call none "f" []) none none none = some (outcome, nextClock) := by
  exact evalPanValueFfiClockProg_call_some evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none) (fun _ => none)
    evaluatorFfi 1 none "f" [] outcome nextClock none none none hcall

/-- A single-word callee return runs the `DecCall` body and restores the local. -/
example
    (hcall : evalPanValueFfiClockCall evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 none "f" [] (preserveReturnLocals := true) =
      some (.control (.returned (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi [.word 5]), 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8 2 (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.decCall "x" .one "f" [] (.annot "tag" "text")) none none none =
    some (panValueFfiClockRestoreLocal "x" none
      (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
        (fun _ => none) (fun _ => none) evaluatorFfi)), 1) := by
  exact evalPanValueFfiClockProg_decCall_returned_some evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 "x" .one "f" [] (.annot "tag" "text")
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi (.word 5) 1
    (.control (.normal (updatePanValueMap (fun _ => none) "x" (.word 5))
      (fun _ => none) (fun _ => none) evaluatorFfi)) 1 none none none hcall
    (by simp [panValueShape, panShapeMatches])
    (evalPanValueFfiClockProg_annot_some evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 0 (updatePanValueMap (fun _ => none) "x" (.word 5))
      (fun _ => none) (fun _ => none) evaluatorFfi 1 "tag" "text" none none none)

/-- The leaf success equation instantiated on `Skip`, whose single-step
    evaluation is `some (.normal ...)`. -/
theorem clocked_leaf_skip_matches_steps :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.skip : Prog Nat) =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 1) := by
  apply evalPanValueFfiClockProg_leaf_some evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi 1 (.skip : Prog Nat) none none none
    PanValueFfiLeafProg.skip
    (.normal (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi) 1
  simp [evalPanValueFfiProgSteps]

/-- The while recursive branch: a nonzero condition and a `normal` body result
    iterate the loop from the body's final state and clock. -/
example
    (nextLocals nextGlobals : VarName → Option (PanValue Nat))
    (nextMemory : Nat → Option (PanValue Nat)) (nextFfi : FfiState Unit)
    (bodyClock : Nat)
    (hbody : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 0 (.break : Prog Nat) none none none =
      some (.control (.normal nextLocals nextGlobals nextMemory nextFfi),
        bodyClock)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.while (.const 5) (.break : Prog Nat))
      none none none =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 1 nextLocals nextGlobals nextMemory nextFfi
      bodyClock (.while (.const 5) (.break : Prog Nat)) none none none := by
  apply evalPanValueFfiClockProg_while_normal_some
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    1 (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.const 5) (.break : Prog Nat) none none none 5
    nextLocals nextGlobals nextMemory nextFfi bodyClock
  · simp [evalPanValueExp]
  · decide
  · decide
  · exact hbody

/-- A terminal (non-normal) first component propagates unchanged through `Seq`. -/
example
    (hfirst : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.raise "E" (.const 1)) none none none =
      some (.control (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi "E" (.word 1)), 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.seq (.raise "E" (.const 1)) (.tick : Prog Nat)) none none none =
      some (.control (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi "E" (.word 1)), 1) := by
  exact evalPanValueFfiClockProg_seq_terminal_some evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none) (fun _ => none)
    evaluatorFfi 1 (.raise "E" (.const 1)) (.tick : Prog Nat)
    (.control (.raised (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi "E" (.word 1))) 1 none none none hfirst
    (by intro l g m f h; cases h)

/-! The same terminal propagation holds at Cake's call-aware `progCallFuel`
    budget, without evaluating the second component. -/
example
    (hfirst : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (progCallFuel 7 (.raise "E" (.const 1) : Prog Nat) +
        progCallFuel 7 (.tick : Prog Nat))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.raise "E" (.const 1)) none none none =
      some (.control (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi "E" (.word 1)), 1)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (progCallFuel 7
        (.seq (.raise "E" (.const 1)) (.tick : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.seq (.raise "E" (.const 1)) (.tick : Prog Nat)) none none none =
      some (.control (.raised (fun _ => none) (fun _ => none) (fun _ => none)
        evaluatorFfi "E" (.word 1)), 1) := by
  exact evalPanValueFfiClockProg_seq_terminal_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.raise "E" (.const 1)) (.tick : Prog Nat)
    (.control (.raised (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi "E" (.word 1))) 1 none none none hfirst
    (by intro l g m f h; cases h)

/-- A nonzero loop condition with an exhausted clock times out. -/
example :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8 2 (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi 0 (.while (.const 5) (.break : Prog Nat)) none none none =
    some (.timeout (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi, 0) := by
  exact evalPanValueFfiClockProg_while_timeout_some evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 1 (fun _ => none)
    (fun _ => none) (fun _ => none) evaluatorFfi 0 (.const 5) (.break : Prog Nat)
    none none none 5 (by simp [evalPanValueExp]) (by decide) (by decide)

/-- The zero-condition `While` succeeds at its structural `progSize` budget. -/
example :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8 (progSize (.while (.const 0) (.break : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi 3 (.while (.const 0) (.break : Prog Nat)) none none none =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 3) := by
  exact evalPanValueFfiClockProg_while_zero_some_progSize evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 (fun _ => none)
    (fun _ => none) (fun _ => none) evaluatorFfi 3 (.const 0) (.break : Prog Nat)
    none none none 0 (by simp [evalPanValueExp]) (by decide)

/-- A `break` inside the body still returns normally at the structural budget. -/
example
    (nextLocals nextGlobals : VarName → Option (PanValue Nat))
    (nextMemory : Nat → Option (PanValue Nat)) (nextFfi : FfiState Unit)
    (bodyClock : Nat)
    (hbody : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 (progSize (.break : Prog Nat))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 0
      (.break : Prog Nat) none none none =
      some (.control (.broke nextLocals nextGlobals nextMemory nextFfi),
        bodyClock)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 (progSize (.while (.const 5) (.break : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.while (.const 5) (.break : Prog Nat)) none none none =
    some (.control (.normal nextLocals nextGlobals nextMemory nextFfi), bodyClock) := by
  exact evalPanValueFfiClockProg_while_broke_some_progSize evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 (fun _ => none)
    (fun _ => none) (fun _ => none) evaluatorFfi 1 (.const 5) (.break : Prog Nat)
    none none none 5 nextLocals nextGlobals nextMemory nextFfi bodyClock
    (by simp [evalPanValueExp]) (by decide) (by decide) hbody

/-- The exhausted-clock timeout also lives at the structural `progSize` budget. -/
example :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8 (progSize (.while (.const 5) (.break : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi 0 (.while (.const 5) (.break : Prog Nat)) none none none =
    some (.timeout (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi, 0) := by
  exact evalPanValueFfiClockProg_while_timeout_some_progSize evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 (fun _ => none)
    (fun _ => none) (fun _ => none) evaluatorFfi 0 (.const 5) (.break : Prog Nat)
    none none none 5 (by simp [evalPanValueExp]) (by decide) (by decide)

/-- The zero-condition `While` also succeeds at the call-aware budget. -/
example :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none) evaluatorHandler
      [] [] 0 0 8 (progCallFuel 7 (.while (.const 0) (.break : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi 3 (.while (.const 0) (.break : Prog Nat)) none none none =
    some (.control (.normal (fun _ => none) (fun _ => none) (fun _ => none)
      evaluatorFfi), 3) := by
  exact evalPanValueFfiClockProg_while_zero_some_progCallFuel evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 (fun _ => none)
    (fun _ => none) (fun _ => none) evaluatorFfi 3 (.const 0) (.break : Prog Nat)
    none none none 0 (by simp [evalPanValueExp]) (by decide)

/-! A continued loop body also re-enters the loop at the call-aware budget. -/
example (bodyClock : Nat)
    (hbody : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 (progCallFuel 7 (.continue : Prog Nat))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 0
      (.continue : Prog Nat) none none none =
      some (.control (.continued (fun _ => none) (fun _ => none)
        (fun _ => none) evaluatorFfi), bodyClock)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (progCallFuel 7 (.while (.const 5) (.continue : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.while (.const 5) (.continue : Prog Nat)) none none none =
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
        evaluatorHandler [] [] 0 0 8 (progCallFuel 7 (.continue : Prog Nat))
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi bodyClock
        (.while (.const 5) (.continue : Prog Nat)) none none none := by
  exact evalPanValueFfiClockProg_while_continued_some_progCallFuel
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.const 5) (.continue : Prog Nat) none none none 5
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi bodyClock
    (by simp [evalPanValueExp]) (by decide) (by decide) hbody

/-! A normal loop body re-enters the loop at the call-aware budget. -/
example (bodyClock : Nat)
    (hbody : evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 (progCallFuel 7 (.skip : Prog Nat))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 0
      (.skip : Prog Nat) none none none =
      some (.control (.normal (fun _ => none) (fun _ => none)
        (fun _ => none) evaluatorFfi), bodyClock)) :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8
      (progCallFuel 7 (.while (.const 5) (.skip : Prog Nat)))
      (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
      (.while (.const 5) (.skip : Prog Nat)) none none none =
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
        evaluatorHandler [] [] 0 0 8 (progCallFuel 7 (.skip : Prog Nat))
        (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi bodyClock
        (.while (.const 5) (.skip : Prog Nat)) none none none := by
  exact evalPanValueFfiClockProg_while_normal_some_progCallFuel
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    (.const 5) (.skip : Prog Nat) none none none 5
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi bodyClock
    (by simp [evalPanValueExp]) (by decide) (by decide) hbody

theorem clocked_seq_normal_exposes_components :
    ∃ (middleLocals middleGlobals : VarName → Option (PanValue Nat))
      (middleMemory : Nat → Option (PanValue Nat)) (middleFfi : FfiState Unit)
      (middleClock : Nat),
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
        evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
        (fun _ => none) evaluatorFfi 2 .tick none none none =
        some (.control (.normal middleLocals middleGlobals middleMemory middleFfi),
          middleClock) ∧
      evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
        evaluatorHandler [] [] 0 0 8 1 middleLocals middleGlobals middleMemory
        middleFfi middleClock .skip none none none =
        some (.control (.normal (fun _ => none) (fun _ => none)
          (fun _ => none) evaluatorFfi), 1) := by
  apply evalPanValueFfiClockProg_seq_normal_some_implies_components_some
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8 1 2
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi
    .tick .skip (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 1
    none none none
  simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
    evalPanValueFfiProgSteps]

theorem clocked_ret_to_tail_common_fuel_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 2
      (retToTail (.seq (.skip : Prog Nat) .tick)) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 2 (.seq .skip .tick) := by
  apply evalPanValueFfiClockProg_retToTail_eq_of_common_fuel
    (fuelTail := 2) (fuelSource := 2) (commonFuel := 2)
    (result := (.control (.normal (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi), 1))
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    (.seq (.skip : Prog Nat) .tick)
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 2
    none none none
  · simp [retToTail, seqCallRet, evalPanValueFfiClockProg,
      evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]
  · simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
      evalPanValueFfiProgSteps]
  · decide
  · decide

theorem clocked_pan_simp_common_fuel_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 2
      (panSimpProg (.seq (.skip : Prog Nat) .tick)) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 2
      (seqAssoc (.skip : Prog Nat) (.seq .skip .tick)) := by
  apply evalPanValueFfiClockProg_panSimpProg_eq_of_common_fuel
    (fuelCompiled := 2) (fuelSource := 2) (commonFuel := 2)
    (result := (.control (.normal (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi), 1))
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    (.seq (.skip : Prog Nat) .tick)
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 2
    none none none
  · simp [panSimpProg, retToTail, seqAssoc, evalPanValueFfiClockProg]
  · simp [seqAssoc, evalPanValueFfiClockProg]
  · decide
  · decide

theorem clocked_pan_simp_source_common_fuel_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 3 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 2
      (panSimpProg (.seq (.skip : Prog Nat) .tick)) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 3 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 2
      (.seq (.skip : Prog Nat) .tick) := by
  apply evalPanValueFfiClockProg_panSimpProg_eq_of_common_fuel_source
    (fuelCompiled := 2) (fuelAssoc := 2) (fuelSource := 2) (commonFuel := 3)
    (result := (.control (.normal (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi), 1))
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    (.seq (.skip : Prog Nat) .tick)
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 2
    none none none
  · simp [panSimpProg, retToTail, seqAssoc, evalPanValueFfiClockProg]
  · simp [seqAssoc, evalPanValueFfiClockProg]
  · simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
      evalPanValueFfiProgSteps]
  · decide
  · decide
  · decide
  · decide

theorem clocked_pan_simp_source_result_common_fuel :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 3 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 2
      (panSimpProg (.seq (.skip : Prog Nat) .tick)) =
    some (.control (.normal (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi), 1) := by
  apply evalPanValueFfiClockProg_panSimpProg_result_of_common_fuel_source
    (fuelCompiled := 2) (fuelAssoc := 2) (fuelSource := 2) (commonFuel := 3)
    (result := (.control (.normal (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi), 1))
    evaluatorContext (fun _ _ => none) evaluatorHandler [] [] 0 0 8
    (.seq (.skip : Prog Nat) .tick)
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi 2
    none none none
  · simp [panSimpProg, retToTail, seqAssoc, evalPanValueFfiClockProg]
  · simp [seqAssoc, evalPanValueFfiClockProg]
  · simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
      evalPanValueFfiProgSteps]
  · decide
  · decide
  · decide
  · decide

theorem pan_simp_skip_seq_fuel_bound_matches_cake :
    panSimpSkipSeqFuel
        (seqAssoc (.skip : Prog Nat)
          (.seq .skip (.seq .skip .skip) : Prog Nat)) ≤
      panSimpSkipSeqFuel (.skip : Prog Nat) +
        panSimpSkipSeqFuel (.seq .skip (.seq .skip .skip) : Prog Nat) := by
  apply panSimpSkipSeqFuel_seqAssoc_le
  · simp [panSimpSkipSeqProg]
  · simp [panSimpSkipSeqProg]

theorem pan_simp_skip_seq_shape_matches_cake :
    panSimpSkipSeqProg
      (seqAssoc (.skip : Prog Nat) (.seq .skip (.seq .skip .skip))) := by
  apply panSimpSkipSeqProg_seqAssoc
  · simp [panSimpSkipSeqProg]
  · simp [panSimpSkipSeqProg]

/-! The expected values are the direct HOL evaluation of
    `pan_simp$SmartSeq` from `pan_simpScript.sml:13-16`. -/
theorem smart_seq_skip_skip :
    smartSeq (.skip : Prog Nat) .skip = .skip := by
  rfl

theorem smart_seq_skip_tick :
    smartSeq (.skip : Prog Nat) .tick = .tick := by
  rfl

theorem smart_seq_tick_skip :
    smartSeq (.tick : Prog Nat) .skip = .seq .tick .skip := by
  rfl

theorem smart_seq_tick_tick :
    smartSeq (.tick : Prog Nat) .tick = .seq .tick .tick := by
  rfl

/-! The expected values are the direct HOL evaluation of
    `pan_simp$seq_assoc` from `pan_simpScript.sml:18-40`. -/
theorem seq_assoc_skip_skip :
    seqAssoc (.skip : Prog Nat) .skip = .skip := by
  simp [seqAssoc]

theorem seq_assoc_tick_skip :
    seqAssoc (.tick : Prog Nat) .skip = .tick := by
  simp [seqAssoc]

theorem seq_assoc_tick_seq_skip_tick :
    seqAssoc (.tick : Prog Nat) (.seq .skip .tick) = .seq .tick .tick := by
  simp [seqAssoc, smartSeq]

theorem seq_assoc_tick_return :
    seqAssoc (.tick : Prog Nat) (.return (.const 7)) =
      .seq .tick (.return (.const 7)) := by
  simp [seqAssoc, smartSeq]

/-! Cake's `exp_ids_seq_assoc_eq` preservation theorem: associating a
sequence does not change the statically reachable exception identifiers. -/
theorem exp_ids_seq_assoc_preserves_raise :
    expIds (seqAssoc (.skip : Prog Nat)
      (.seq (.raise "E" (.const 0)) .tick)) = ["E"] := by
  simpa [expIds] using expIds_seqAssoc (.skip : Prog Nat)
    (.seq (.raise "E" (.const 0)) .tick)

/-! Cake's `exp_ids_ret_to_tail_eq` preservation theorem, exercised through
    a nested call handler as well as the outer program. -/
theorem exp_ids_ret_to_tail_preserves_raise :
    expIds (retToTail (.raise "E" (.const 0) : Prog Nat)) = ["E"] := by
  simpa [expIds] using expIds_retToTail
    (.raise "E" (.const 0) : Prog Nat)

theorem exp_ids_ret_to_tail_preserves_nested_raise :
    expIds (retToTail
      (.call
        (some (some (VarKind.local, "r"), some ("E", "h",
          .seq (.raise "E2" (.const 0)) .tick)))
        "f" [] : Prog Nat)) = ["E", "E2"] := by
  simpa [expIds] using expIds_retToTail
    (.call
      (some (some (VarKind.local, "r"), some ("E", "h",
        .seq (.raise "E2" (.const 0)) .tick)))
      "f" [] : Prog Nat)

/-! The expected values are the direct HOL evaluation of
    `pan_simp$seq_call_ret` from `pan_simpScript.sml:42-49`. -/
theorem seq_call_ret_matching_return :
    seqCallRet
        (.seq
          (.call (some (some (VarKind.local, "r"), none)) "f" [])
          (.return (.var .local "r")) : Prog Nat) =
      .call none "f" [] := by
  simp [seqCallRet]

theorem seq_call_ret_mismatching_return :
    seqCallRet
        (.seq
          (.call (some (some (VarKind.local, "r"), none)) "f" [])
          (.return (.var .local "s")) : Prog Nat) =
      .seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "s")) := by
  simp [seqCallRet]

theorem seq_call_ret_fallback :
    seqCallRet (.tick : Prog Nat) = .tick := by
  rfl


/-! The expected values are the direct HOL evaluation of
    `pan_simp$ret_to_tail` from `pan_simpScript.sml:50-66`. -/
theorem ret_to_tail_skip :
    retToTail (.skip : Prog Nat) = .skip := by
  simp [retToTail]

theorem ret_to_tail_matching_return :
    retToTail
        (.seq
          (.call (some (some (VarKind.local, "r"), none)) "f" [])
          (.return (.var .local "r")) : Prog Nat) =
      .call none "f" [] := by
  simp [retToTail, seqCallRet]

theorem ret_to_tail_mismatching_return :
    retToTail
        (.seq
          (.call (some (some (VarKind.local, "r"), none)) "f" [])
          (.return (.var .local "s")) : Prog Nat) =
      .seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "s")) := by
  simp [retToTail, seqCallRet]

/- The HOL handler fixture uses exception id `0`; Lean's `ExceptionId` is a
   string, so the parity witness normalizes that identifier to `"E"`. -/
theorem ret_to_tail_handler_seq :
    retToTail
        (.call
          (some (some (VarKind.local, "r"), some ("E", "h", .seq .tick .tick)))
          "f" [] : Prog Nat) =
      .call
        (some (some (VarKind.local, "r"), some ("E", "h", .seq .tick .tick)))
        "f" [] := by
  simp [retToTail, seqCallRet]

/-! The expected values are the direct HOL evaluation of
    `pan_simp$compile` from `pan_simpScript.sml:68-72`. -/
theorem pan_simp_compile_skip :
    panSimpProg (.skip : Prog Nat) = .skip := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem pan_simp_compile_seq_skip_tick :
    panSimpProg (.seq (.skip : Prog Nat) .tick) = .tick := by
  simp [panSimpProg, seqAssoc, retToTail, smartSeq]

theorem pan_simp_compile_tail_call :
    panSimpProg
        (.seq
          (.call (some (some (VarKind.local, "r"), none)) "f" [])
          (.return (.var .local "r")) : Prog Nat) =
      .call none "f" [] := by
  simp [panSimpProg, seqAssoc, retToTail, seqCallRet, smartSeq]

def isSkip : Prog Nat → Bool
  | .skip => true
  | _ => false

def isTick : Prog Nat → Bool
  | .tick => true
  | _ => false

def isTickSkip : Prog Nat → Bool
  | .seq .tick .skip => true
  | _ => false

def isTickTick : Prog Nat → Bool
  | .seq .tick .tick => true
  | _ => false

def isTickReturn : Prog Nat → Bool
  | .seq .tick (.return (.const 7)) => true
  | _ => false

def isTailCall : Prog Nat → Bool
  | .call none "f" [] => true
  | _ => false

def isMismatchingCall : Prog Nat → Bool
  | .seq
      (.call (some (some (VarKind.local, "r"), none)) "f" [])
      (.return (.var .local "s")) => true
  | _ => false

def isHandlerSeq : Prog Nat → Bool
  | .call
      (some (some (VarKind.local, "r"), some ("E", "h", .seq .tick .tick)))
      "f" [] => true
  | _ => false

/-! `pan_simp$compile_prog` (`pan_simpScript.sml:74-81`) maps `compile` over
    function declarations and preserves every non-function declaration. -/
def compileProgDeclsFixture : List (Decl Nat) :=
  [.decl .one "g" (.const 7),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .seq .skip .tick, returnShape := .one }]

def compileProgDeclsParity : Bool :=
  match panSimpDecls compileProgDeclsFixture with
  | [.decl .one "g" (.const 7), .function declaration] =>
      match declaration.body with
      | .tick => true
      | _ => false
  | _ => false

#guard compileProgDeclsParity

theorem pan_simp_compile_prog_map :
    panSimpDecls compileProgDeclsFixture =
      compileProgDeclsFixture.map panSimpDecl := by
  exact panSimpDecls_eq_map compileProgDeclsFixture

theorem pan_simp_compile_prog_size_of_eids :
    sizeOfEids (panSimpDecls compileProgDeclsFixture) =
      sizeOfEids compileProgDeclsFixture := by
  exact sizeOfEids_panSimpDecls compileProgDeclsFixture

theorem pan_simp_compile_prog_functions :
    functions (panSimpDecls compileProgDeclsFixture) =
      (functions compileProgDeclsFixture).map (fun entry =>
        (entry.1, entry.2.1, panSimpProg entry.2.2.1, entry.2.2.2)) := by
  exact functions_panSimpDecls compileProgDeclsFixture

theorem pan_simp_compile_prog_first_all_distinct :
    ((functions (panSimpDecls compileProgDeclsFixture)).map
      (fun entry => entry.1)).Nodup := by
  exact functions_panSimpDecls_names_nodup compileProgDeclsFixture (by decide)

theorem pan_simp_compile_prog_distinct_params :
    ∀ entry ∈ functions (panSimpDecls compileProgDeclsFixture),
      (entry.2.1.map Prod.fst).Nodup := by
  apply functions_panSimpDecls_params_nodup compileProgDeclsFixture
  intro entry hentry
  simp [compileProgDeclsFixture, functions, functionEntries] at hentry
  rcases hentry with rfl
  simp

def functionsNamesNodupParity : Bool :=
  decide (((functions (panSimpDecls compileProgDeclsFixture)).map
    (fun entry => entry.1)).Nodup)

#guard functionsNamesNodupParity

def functionsCompileProgParity : Bool :=
  match functions (panSimpDecls compileProgDeclsFixture) with
  | [(name, params, body, returnShape)] =>
      (name == "f") && params.isEmpty &&
        (match body with | .tick => true | _ => false) &&
        (match returnShape with | .one => true | _ => false)
  | _ => false

#guard functionsCompileProgParity

/-! Counterpart of Cake's `functions_eq_FILTER`
    (`panPropsScript.sml:1487`): the function table is the filter-map of the
    function declarations. -/
theorem functions_eq_filterMap_fixture :
    functions compileProgDeclsFixture =
      compileProgDeclsFixture.filterMap (fun declaration =>
        match declaration with
        | .function function =>
            some (function.name, function.params, function.body,
              function.returnShape)
        | _ => none) :=
  functions_eq_filterMap compileProgDeclsFixture

def functionsFilterMapGuard : Bool :=
  (functions compileProgDeclsFixture).length == 1

#eval functionsFilterMapGuard
#guard functionsFilterMapGuard

/-! Counterpart of Cake's `el_compile_prog_el_prog_eq`
    (`pan_simpProofScript.sml:1047-1061`): an entry of the compiled function
    table still comes from the source table, because `pan_simp` only rewrites
    bodies.  The fixture uses a `.skip` body so the transformed body is the
    source body. -/
def elCompileProgDeclsFixture : List (Decl Nat) :=
  [.function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .one }]

theorem pan_simp_compile_prog_el_compile_prog_el_prog_eq :
    (functions elCompileProgDeclsFixture)[0]? =
      some ("f", [], .skip, .one) := by
  have hentry : (functions (panSimpDecls elCompileProgDeclsFixture))[0]? =
      some ("f", [], .skip, .one) := by
    rw [functions_panSimpDecls, List.getElem?_map]
    rw [show (functions elCompileProgDeclsFixture)[0]? =
      some ("f", [], .skip, .one) from rfl]
    simp only [Option.map_some, panSimpProg_skip]
  exact el_functions_panSimpDecls_eq
    (declarations := elCompileProgDeclsFixture)
    (n := 0) (start := "f") (pprog := .skip) (p := .skip)
    (rshape := .one) hentry (by decide) (by decide) (by rfl)

def functionsElCompileParity : Bool :=
  match (functions elCompileProgDeclsFixture)[0]? with
  | some (name, params, body, returnShape) =>
      (name == "f") && params.isEmpty &&
        (match body with | .skip => true | _ => false) &&
        (match returnShape with | .one => true | _ => false)
  | _ => false

#guard functionsElCompileParity

def parityGuard : Bool :=
  isSkip (smartSeq (.skip : Prog Nat) .skip) &&
    isTick (smartSeq (.skip : Prog Nat) .tick) &&
    isTickSkip (smartSeq (.tick : Prog Nat) .skip) &&
    isTickTick (smartSeq (.tick : Prog Nat) .tick) &&
    isSkip (seqAssoc (.skip : Prog Nat) .skip) &&
    isTick (seqAssoc (.tick : Prog Nat) .skip) &&
    isTickTick (seqAssoc (.tick : Prog Nat) (.seq .skip .tick)) &&
    isTickReturn (seqAssoc (.tick : Prog Nat) (.return (.const 7))) &&
    isTailCall (seqCallRet
      (.seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "r")) : Prog Nat)) &&
    isMismatchingCall (seqCallRet
      (.seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "s")) : Prog Nat)) &&
    isTick (seqCallRet (.tick : Prog Nat)) &&
    isSkip (retToTail (.skip : Prog Nat)) &&
    isTailCall (retToTail
      (.seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "r")) : Prog Nat)) &&
    isMismatchingCall (retToTail
      (.seq
        (.call (some (some (VarKind.local, "r"), none)) "f" [])
        (.return (.var .local "s")) : Prog Nat)) &&
    isHandlerSeq (retToTail
      (.call
        (some (some (VarKind.local, "r"), some ("E", "h", .seq .tick .tick)))
        "f" [] : Prog Nat)) &&
    isSkip (panSimpProg (.skip : Prog Nat)) &&
    isTick (panSimpProg (.seq (.skip : Prog Nat) .tick)) &&
    isTailCall (panSimpProg
      (.seq
            (.call (some (some (VarKind.local, "r"), none)) "f" [])
            (.return (.var .local "r")) : Prog Nat)) &&
    functionsCompileProgParity &&
    functionsNamesNodupParity &&
    functionsElCompileParity

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS pan_simp SmartSeq/seq_assoc/seq_call_ret/ret_to_tail/compile source parity"
  else
    IO.println "FAIL pan_simp SmartSeq/seq_assoc/seq_call_ret/ret_to_tail/compile source parity"
  IO.println "PASS pan_simp clocked evaluate_seq_skip/evaluate_skip_seq Cake equations"
  IO.println "PASS pan_simp clocked evaluate_while_body_same Cake equation"
  IO.println "PASS pan_simp clocked evaluate_seq_second_congr Cake equation"
  IO.println "PASS pan_simp clocked evaluate_seq_normal_components Cake equation"
  IO.println "PASS pan_simp clocked terminal Seq progCallFuel Cake equation"
  IO.println "PASS pan_simp caught-handler normal progCallFuel Cake equation"
  IO.println "PASS pan_simp clocked continued While progCallFuel Cake equation"
  IO.println "PASS pan_simp clocked normal While progCallFuel Cake equation"
  IO.println "PASS pan_simp Skip/Seq fuel-adequacy fragment Cake bound"
  IO.println "PASS pan_simp clocked ret_to_tail common-fuel Cake equation"
  IO.println "PASS pan_simp clocked pan_simp common-fuel Cake equation"
  IO.println "PASS pan_simp clocked transformed result common-fuel Cake equation"
  IO.println "PASS pan_simp functions_compile_prog Cake function-table equation"
  IO.println "PASS pan_simp first_compile_prog_all_distinct Cake name-distinctness preservation"
  IO.println "PASS pan_simp el_compile_prog_el_prog_eq Cake compiled-table entry provenance"
  IO.println "PASS pan_simp functions_eq_FILTER Cake function-table filter-map equation"
  pure parityGuard

/-! A nonzero-condition `While` whose body breaks exits normally, certified by the
fuel-indexed exit certificate. -/
example : PanValueFfiClockNormalAdequateProgFrom 1 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.while (.const 5) (.break : Prog Nat)) :=
  PanValueFfiClockNormalAdequateProgFrom_while 1 evaluatorContext (fun _ _ => none)
    evaluatorHandler [] [] 0 0 8 7 none none none (.const 5) (.break : Prog Nat)
    (fun clock hclock locals globals memory ffi => by
      have hclockNe : (clock == 0) = false := by
        cases hb : (clock == 0) with
        | false => rfl
        | true =>
            rw [beq_iff_eq] at hb
            omega
      simp only [progCallFuel, PanValueFfiClockWhileExitsNormally]
      exact Or.inr (Or.inr ⟨5, by simp [evalPanValueExp], by decide, hclockNe,
        locals, globals, memory, ffi, decPanClock clock, by
          simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
            evalPanValueFfiProgSteps]⟩))

/-! The fuel-indexed while-exit certificate underpinning the nonzero-condition
`While` adequacy constructor. -/

/-! A lower-bound-preserving sequence certificate.  Both `Skip` components
    leave the clock unchanged, so the new floor-composition theorem can feed
    the first result directly into the continuation's lower-bound premise. -/
example : PanValueFfiClockNormalAdequateProgFromFloor 0 0 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.seq (.skip : Prog Nat) .skip) := by
  refine PanValueFfiClockNormalAdequateProgFromFloor_seq
    (lo := 0) (firstFloor := 0) (finalFloor := 0)
    (context := evaluatorContext) (primitive := fun _ _ => none)
    (handler := evaluatorHandler) (structs := []) (functions := [])
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8)
    (callBudget := 7) (ma := none) (c := none) (mh := none)
    (first := (.skip : Prog Nat)) (second := (.skip : Prog Nat)) ?_ ?_
  all_goals
    intro clock _ locals globals memory ffi
    exact ⟨locals, globals, memory, ffi, clock, by
      simp [progCallFuel, evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
        evalPanValueFfiProgSteps], by omega⟩

/-! Discharging the explicit floor premise: an adequate (clock-unbounded)
    program has trivial floor `0`, the input bound can be raised, and a
    lower-bounded first program composes with an adequate continuation. -/

/-! Clock-free annotations also keep their floor. -/
example : PanValueFfiClockNormalAdequateProgFromFloor 0 0 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.annot "tag" "text") :=
  PanValueFfiClockNormalAdequateProgFromFloor_annot 0 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none "tag" "text"

/-! The clock-free leaf preserves its floor, giving the floor-composition
    theorem a base case; declarations and conditionals then preserve it. -/
example : PanValueFfiClockNormalAdequateProgFromFloor 0 0 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.skip : Prog Nat) :=
  PanValueFfiClockNormalAdequateProgFromFloor_leaf 0 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none (.skip : Prog Nat)
    PanValueFfiLeafProg.skip
    (by
      intro locals globals memory ffi
      exact ⟨locals, globals, memory, ffi, 1, by simp [evalPanValueFfiProgSteps]⟩)

example : PanValueFfiClockNormalAdequateProgFromFloor 0 0 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.dec "x" .one (.const 5) (.skip : Prog Nat)) := by
  refine PanValueFfiClockNormalAdequateProgFromFloor_dec 0 0 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none "x" .one
    (.const 5) (.skip : Prog Nat) ?_ ?_
  · intro locals globals memory
    exact ⟨.word 5, by simp [evalPanValueExp],
      by simp [panValueShape, panShapeMatches]⟩
  · exact PanValueFfiClockNormalAdequateProgFromFloor_leaf 0 evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.skip : Prog Nat) PanValueFfiLeafProg.skip
      (by
        intro locals globals memory ffi
        exact ⟨locals, globals, memory, ffi, 1, by simp [evalPanValueFfiProgSteps]⟩)

example : PanValueFfiClockNormalAdequateProgFromFloor 0 0 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.ite (.const 5) (.skip : Prog Nat) (.skip : Prog Nat)) := by
  have hskip : PanValueFfiClockNormalAdequateProgFromFloor 0 0 evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.skip : Prog Nat) :=
    PanValueFfiClockNormalAdequateProgFromFloor_leaf 0 evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.skip : Prog Nat) PanValueFfiLeafProg.skip
      (by
        intro locals globals memory ffi
        exact ⟨locals, globals, memory, ffi, 1, by simp [evalPanValueFfiProgSteps]⟩)
  exact PanValueFfiClockNormalAdequateProgFromFloor_ite 0 0 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none (.const 5)
    (.skip : Prog Nat) (.skip : Prog Nat) (fun _ _ _ => ⟨5, by simp [evalPanValueExp]⟩)
    hskip hskip

/-! A tick lowers the floor by one, and the floor-composition theorem then feeds
    the lowered floor into a clock-free continuation. -/
example : PanValueFfiClockNormalAdequateProgFromFloor 1 0 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.seq (.tick : Prog Nat) (.skip : Prog Nat)) := by
  refine PanValueFfiClockNormalAdequateProgFromFloor_seq (lo := 1) (firstFloor := 0)
    (finalFloor := 0) (context := evaluatorContext) (primitive := fun _ _ => none)
    (handler := evaluatorHandler) (structs := []) (functions := [])
    (baseAddress := 0) (topAddress := 0) (bytesInWord := 8) (callBudget := 7)
    (ma := none) (c := none) (mh := none)
    (first := (.tick : Prog Nat)) (second := (.skip : Prog Nat)) ?_ ?_
  · exact PanValueFfiClockNormalAdequateProgFromFloor_tick 1 (by decide) evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
  · exact PanValueFfiClockNormalAdequateProgFromFloor_leaf 0 evaluatorContext
      (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
      (.skip : Prog Nat) PanValueFfiLeafProg.skip
      (by
        intro locals globals memory ffi
        exact ⟨locals, globals, memory, ffi, 1, by simp [evalPanValueFfiProgSteps]⟩)

/-- The inductive normal fragment enters the floor certificate at `floor = lo`. -/
example : PanValueFfiClockNormalAdequateProgFromFloor 3 3 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.seq (.skip : Prog Nat) (.annot "tag" "text")) :=
  PanValueFfiClockNormalAdequateProgFromFloor_of_normalProg 3 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.seq (.skip : Prog Nat) (.annot "tag" "text"))
    (PanValueFfiClockNormalProg.seq (.skip : Prog Nat) (.annot "tag" "text")
      PanValueFfiClockNormalProg.skip (PanValueFfiClockNormalProg.annot "tag" "text"))


/-- The pan_simp transform of a normal program keeps a floor certificate. -/
example : PanValueFfiClockNormalAdequateProgFromFloor 3 3 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (panSimpProg (.seq (.skip : Prog Nat) (.annot "tag" "text"))) :=
  PanValueFfiClockNormalAdequateProgFromFloor_panSimpProg 3 evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 7 none none none
    (.seq (.skip : Prog Nat) (.annot "tag" "text"))
    (PanValueFfiClockNormalProg.seq (.skip : Prog Nat) (.annot "tag" "text")
      PanValueFfiClockNormalProg.skip (PanValueFfiClockNormalProg.annot "tag" "text"))


-- Clock-shift arithmetic needed by a whole-program analogue of Cake
-- `evaluate_add_clock_eq`.


/-! ## Exact HOL helper-slice instantiations

These instantiate the tagged HOL helper restatements in
`Flapjack/Pancake/Proofs/PanSimp.lean` at a concrete word type so the reviewed
statements are exercised by `lake build`. -/

example : expIds (retToTail (.skip : Prog Nat)) = expIds (.skip : Prog Nat) :=
  expIdsRetToTailEq .skip

example : expIds (seqAssoc (.skip : Prog Nat) (.skip : Prog Nat)) =
    expIds (.skip : Prog Nat) ++ expIds (.skip : Prog Nat) :=
  expIdsSeqAssocEq .skip .skip

example : expIds (panSimpProg (.skip : Prog Nat)) = expIds (.skip : Prog Nat) :=
  expIdsCompileEq .skip

example : sizeOfEids (panSimpDecls ([] : List (Decl Nat))) =
    sizeOfEids ([] : List (Decl Nat)) :=
  sizeOfEidsPanSimpDeclsEq []

example : functions (panSimpDecls ([] : List (Decl Nat))) =
    (functions ([] : List (Decl Nat))).map (fun entry =>
      (entry.1, entry.2.1, panSimpProg entry.2.2.1, entry.2.2.2)) :=
  functionsCompileProg []

example : ((functions (panSimpDecls ([] : List (Decl Nat)))).map
    (fun entry => entry.1)).Nodup :=
  firstCompileProgAllDistinctPanSimp [] (by simp [functions, functionEntries])

example :
    ([(1, (2, 3))] : List (Nat × Nat × Nat)).map (fun entry => entry.2.2 + 1) =
      (([(1, (2, 3))] : List (Nat × Nat × Nat)).map
        (fun entry => entry.2.2)).map (fun body => body + 1) :=
  mapSndFEq _ (fun body => body + 1) (fun value => value)


end Flapjack.Test.PanSimpParity
