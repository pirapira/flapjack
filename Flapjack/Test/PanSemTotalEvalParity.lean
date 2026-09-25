import Flapjack.Pancake.Semantics.PanSem.TotalEval
import Flapjack.Test.PanSemTotalParity

/-! Regression checks for the measured total evaluator's real `Prog.ite` branch.
    Expected branch and error outcomes come from the original HOL rows in
    `scripts/hol-probes/pan_sem_ite_e2e_probe.out`. -/

namespace Flapjack.Test.PanSemTotalEvalParity

open Flapjack
open Flapjack.RiscV
open Flapjack.Test.PanSemTotalParity

private abbrev Word64 := Word 64

private def evaluate (program : Prog Word64)
    (state : PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateTotalRiscV64 (fun _ _ => none) program state

private def isStructEmptyOption (value : Option (PanValue Word64)) : Bool :=
  match value with
  | some (.rStruct []) => true
  | _ => false

private def totalIdCode : PanSemCodeMap Word64 :=
  [("id", ([("x", .one)],
    .return (.var .local "x"), .one))]

private def totalNestedCallCode : PanSemCodeMap Word64 :=
  [("outer", ([], .call none "id" [], .one)),
   ("id", ([], .return (.const (BitVec.ofNat 64 7)), .one))]

private def totalDecCallState : PanSemState Word64 (FfiState Unit) :=
  { totalIfState with clock := 10, code := totalIdCode }

private def totalNestedCallState : PanSemState Word64 (FfiState Unit) :=
  { totalIfState with clock := 10, code := totalNestedCallCode }

private def totalIfNonwordValueState : PanSemState Word64 (FfiState Unit) :=
  { totalIfState with
    locals := updatePanValueMap totalIfState.locals "y" (.rStruct []) }

def ifTrueTickGuard : Bool :=
  match evaluate (.ite (.const (BitVec.ofNat 64 1)) .tick .skip) totalIfState with
  | (none, state) => state.clock == 4 && isWordOption 3 (state.locals "x")
  | _ => false

def ifFalseTickGuard : Bool :=
  match evaluate (.ite (.const (BitVec.ofNat 64 0)) .tick .skip) totalIfState with
  | (none, state) => state.clock == 5 && isWordOption 3 (state.locals "x")
  | _ => false

def ifMissingConditionGuard : Bool :=
  match evaluate (.ite (.var .local "z") .tick .skip) totalIfState with
  | (some .error, state) => state.clock == 5 &&
      isWordOption 3 (state.locals "x") && (state.locals "z").isNone
  | _ => false

def ifNonwordConditionGuard : Bool :=
  match evaluate (.ite (.var .local "y") .tick .skip) totalIfNonwordValueState with
  | (some .error, state) => state.clock == 5 &&
      isWordOption 3 (state.locals "x") && isStructEmptyOption (state.locals "y")
  | _ => false

def ifLoadFailureGuard : Bool :=
  match evaluate (.ite (.load .one (.const (BitVec.ofNat 64 0))) .tick .skip)
      totalIfState with
  | (some .error, state) => state.clock == 5 &&
      isWordOption 3 (state.locals "x") &&
        (state.memory (BitVec.ofNat 64 0)).isNone
  | _ => false

def callCodeMapGuard : Bool :=
  match evaluate (.call none "id" [.const (BitVec.ofNat 64 7)]) totalDecCallState with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 7 && state.clock == 9 &&
        (state.locals "x").isNone
  | _ => false

def decCallCodeMapGuard : Bool :=
  match evaluate
      (.decCall "answer" .one "id" [.const (BitVec.ofNat 64 7)]
        (.return (.var .local "answer"))) totalDecCallState with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 7 && state.clock == 9 &&
        (state.locals "answer").isNone
  | _ => false

def nestedCallCodeMapGuard : Bool :=
  match evaluate (.call none "outer" []) totalNestedCallState with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 7 && state.clock == 8
  | _ => false

#guard ifTrueTickGuard
#guard ifFalseTickGuard
#guard ifMissingConditionGuard
#guard ifNonwordConditionGuard
#guard ifLoadFailureGuard
#guard callCodeMapGuard
#guard decCallCodeMapGuard
#guard nestedCallCodeMapGuard

def runChecks : IO Bool := do
  if ifTrueTickGuard then
    IO.println "PASS full Prog total evaluator If true selects Tick from direct HOL oracle"
  else IO.println "FAIL full Prog total evaluator If true selects Tick from direct HOL oracle"
  if ifFalseTickGuard then
    IO.println "PASS full Prog total evaluator If false selects Skip from direct HOL oracle"
  else IO.println "FAIL full Prog total evaluator If false selects Skip from direct HOL oracle"
  if ifMissingConditionGuard && ifNonwordConditionGuard && ifLoadFailureGuard then
    IO.println "PASS full Prog total evaluator If errors preserve state against direct HOL oracle"
  else IO.println "FAIL full Prog total evaluator If errors preserve state against direct HOL oracle"
  if callCodeMapGuard && decCallCodeMapGuard && nestedCallCodeMapGuard then
    IO.println "PASS full Prog total evaluator recursive Call/DecCall read state-owned code against direct HOL rows"
  else IO.println "FAIL full Prog total evaluator recursive Call/DecCall read state-owned code against direct HOL rows"
  pure (ifTrueTickGuard && ifFalseTickGuard && ifMissingConditionGuard &&
    ifNonwordConditionGuard && ifLoadFailureGuard && callCodeMapGuard &&
    decCallCodeMapGuard && nestedCallCodeMapGuard)

end Flapjack.Test.PanSemTotalEvalParity
