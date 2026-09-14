import Flapjack.PanObservationalSemantics
import Flapjack.Test.PanValueFfiSemantics

/-!
# Source parity for Pancake `semantics_def`

The source reference is `panSemScript.sml:785-809`.  The direct HOL
`pan_sem_e2e_probe.out` fixture supplies the finite `evaluate` observations
used by the source semantics (`Return`, conditional, call, memory, and FFI).
These checks exercise the observation wrapper's fail, successful return,
successful final-FFI, and divergence/LUB branches, while `sourceClockParity`
executes the source-shaped entry call through `panSemEvaluate`.
-/

namespace Flapjack.Test.PanObservationalSemanticsParity

open Flapjack
open Flapjack.RiscV

def emptyLocals : VarName → Option (PanValue (Word 64)) := fun _ => none
def emptyMemory : Word 64 → Option (PanValue (Word 64)) := fun _ => none

def sourceFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("main", [], .return (.const (BitVec.ofNat 64 41)))]

def sourceContracts : PanValueCallContracts :=
  PanValueCallContracts.mk [("main", .one)] [] [("main", [])]

def sourceState (clock : Nat) : PanSemEvaluateState (Word 64) Unit :=
  { structs := []
    functions := sourceFunctions
    locals := emptyLocals
    globals := fun _ => none
    memory := emptyMemory
    ffi := statefulTestFfiState
    clock := clock
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100
    bytesInWord := BitVec.ofNat 64 8
    contracts := some sourceContracts }

def sourceEvaluate (clock : Nat) :=
  panSemEvaluate statefulTestContext statefulTestPrimitive statefulTestHandler
    (sourceState clock) (.call none "main" [] : Prog (Word 64))

def sourceClockParity : Bool :=
  match sourceEvaluate 0, sourceEvaluate 1 with
  | some (.timeout _ _ _ _, 0),
      some (.control (.returned _ _ _ _ [PanValue.word value]), 0) =>
      value == BitVec.ofNat 64 41
  | _, _ => false

theorem emptyPrefixChain : panLprefixChain (fun _ : Nat => ([] : List FfiEvent)) :=
  fun _ _ => Or.inl (List.prefix_refl [])

def emptyLprefixLub : PanLprefixLub (fun _ : Nat => ([] : List FfiEvent)) :=
  { trace := fun _ => none
    isLub := by
      constructor
      · intro _clock index value hvalue
        simp at hvalue
      · intro _candidate _hbound index value htrace
        simp at htrace }

def emptyFfi : FfiState Unit := statefulTestFfiState

def hooksFor (evaluate : Nat → Option (PanValueFfiClockResult (Word 64) Unit)) :
    PanSemanticsHooks (Word 64) Unit :=
  { evaluate := evaluate
    ffiOutcome := fun event => event.outcome }

def successEvaluate (clock : Nat) : Option (PanValueFfiClockResult (Word 64) Unit) :=
  if clock = 0 then
    some (.timeout emptyLocals (fun _ => none) emptyMemory emptyFfi, 0)
  else
    some (.control (.returned emptyLocals (fun _ => none) emptyMemory emptyFfi
      [PanValue.word (BitVec.ofNat 64 1)]), clock - 1)

def forbiddenEvaluate (_clock : Nat) : Option (PanValueFfiClockResult (Word 64) Unit) :=
  none

def divergingEvaluate (_clock : Nat) :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  some (.timeout emptyLocals (fun _ => none) emptyMemory emptyFfi, 0)

def finalFfiEvaluate (_clock : Nat) :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  some (.control (.finalFfi emptyLocals (fun _ => none) emptyMemory emptyFfi
    { name := .sharedMem .mappedRead
      configuration := []
      bytes := []
      outcome := .failed }), 0)

noncomputable def lprefixLubFor
    (evaluate : Nat → Option (PanValueFfiClockResult (Word 64) Unit))
    (chain : panLprefixChain (fun clock => panResultEvents (evaluate clock))) :
    PanLprefixLub (fun clock => panResultEvents (evaluate clock)) :=
  buildPanLprefixLub _ chain

theorem successPrefixChain :
    panLprefixChain (fun clock => panResultEvents (successEvaluate clock)) := by
  intro left right
  by_cases hleft : left = 0 <;> by_cases hright : right = 0 <;>
    simp [successEvaluate, panResultEvents, panResultFfi, hleft, hright]

theorem forbiddenPrefixChain :
    panLprefixChain (fun clock => panResultEvents (forbiddenEvaluate clock)) := by
  intro left right
  exact Or.inl (by simp [forbiddenEvaluate, panResultEvents])

theorem divergingPrefixChain :
    panLprefixChain (fun clock => panResultEvents (divergingEvaluate clock)) := by
  intro left right
  exact Or.inl (by simp [divergingEvaluate, panResultEvents])

theorem finalFfiPrefixChain :
    panLprefixChain (fun clock => panResultEvents (finalFfiEvaluate clock)) := by
  intro left right
  exact Or.inl (by simp [finalFfiEvaluate, panResultEvents])

theorem successBranch : panHasSuccessfulRun (hooksFor successEvaluate) := by
  refine ⟨1, (.control (.returned emptyLocals (fun _ => none) emptyMemory emptyFfi
    [PanValue.word (BitVec.ofNat 64 1)]), 0), .success, ?_, ?_⟩
  · rfl
  · rfl

theorem successNoForbidden :
    ¬ panHasForbiddenRun (hooksFor successEvaluate) := by
  rintro ⟨clock, hclock⟩
  cases clock with
  | zero =>
      change panForbiddenResult (successEvaluate 0) at hclock
      simp [successEvaluate, panForbiddenResult] at hclock
  | succ clock =>
      change panForbiddenResult (successEvaluate (clock + 1)) at hclock
      simp [successEvaluate, panForbiddenResult] at hclock

theorem finalFfiBranch : panHasSuccessfulRun (hooksFor finalFfiEvaluate) := by
  refine ⟨0, (.control (.finalFfi emptyLocals (fun _ => none) emptyMemory emptyFfi
    { name := .sharedMem .mappedRead
      configuration := []
      bytes := []
      outcome := .failed }), 0), .ffi .failed, ?_, ?_⟩
  · rfl
  · rfl

theorem finalFfiNoForbidden :
    ¬ panHasForbiddenRun (hooksFor finalFfiEvaluate) := by
  rintro ⟨clock, hclock⟩
  change panForbiddenResult (finalFfiEvaluate clock) at hclock
  simp [finalFfiEvaluate, panForbiddenResult] at hclock

theorem forbiddenBranch :
    panHasForbiddenRun (hooksFor forbiddenEvaluate) := by
  exact ⟨0, by
    change panForbiddenResult (forbiddenEvaluate 0)
    simp [forbiddenEvaluate, panForbiddenResult]⟩

theorem divergenceBranch :
    ¬ panHasForbiddenRun (hooksFor divergingEvaluate) ∧
      ¬ panHasSuccessfulRun (hooksFor divergingEvaluate) := by
  constructor
  · rintro ⟨clock, hclock⟩
    change panForbiddenResult (divergingEvaluate clock) at hclock
    simp [divergingEvaluate, panForbiddenResult] at hclock
  · rintro ⟨clock, result, outcome, heval, houtcome⟩
    change divergingEvaluate clock = some result at heval
    cases heval
    simp [panResultOutcome] at houtcome

theorem semanticsForbidden :
    panSemanticsWithLub (hooksFor forbiddenEvaluate)
      (lprefixLubFor forbiddenEvaluate forbiddenPrefixChain) = .fail := by
  classical
  simp [panSemanticsWithLub, forbiddenBranch]

theorem semanticsSuccess :
    panSemanticsWithLub (hooksFor successEvaluate)
      (lprefixLubFor successEvaluate successPrefixChain) =
      panChooseTermination (hooksFor successEvaluate) successBranch := by
  classical
  by_cases forbidden : panHasForbiddenRun (hooksFor successEvaluate)
  · exact (successNoForbidden forbidden).elim
  · by_cases successful : panHasSuccessfulRun (hooksFor successEvaluate)
    · simp [panSemanticsWithLub, forbidden, successful]
    · exact (successful successBranch).elim

theorem semanticsFinalFfi :
    panSemanticsWithLub (hooksFor finalFfiEvaluate)
      (lprefixLubFor finalFfiEvaluate finalFfiPrefixChain) =
      panChooseTermination (hooksFor finalFfiEvaluate) finalFfiBranch := by
  classical
  by_cases forbidden : panHasForbiddenRun (hooksFor finalFfiEvaluate)
  · exact (finalFfiNoForbidden forbidden).elim
  · by_cases successful : panHasSuccessfulRun (hooksFor finalFfiEvaluate)
    · simp [panSemanticsWithLub, forbidden, successful]
    · exact (successful finalFfiBranch).elim

theorem semanticsDivergence :
    panSemanticsWithLub (hooksFor divergingEvaluate)
      (lprefixLubFor divergingEvaluate divergingPrefixChain) =
      .diverge (fun _ => []) (lprefixLubFor divergingEvaluate divergingPrefixChain) := by
  classical
  by_cases forbidden : panHasForbiddenRun (hooksFor divergingEvaluate)
  · exact (divergenceBranch.1 forbidden).elim
  · by_cases successful : panHasSuccessfulRun (hooksFor divergingEvaluate)
    · exact (divergenceBranch.2 successful).elim
    · simp only [panSemanticsWithLub, dif_neg forbidden, dif_neg successful]
      congr 2

theorem semanticsCanonicalDivergence :
    panSemantics (hooksFor divergingEvaluate)
      (by
        intro _ _
        exact Or.inl (List.prefix_refl [])) =
      .diverge (fun _ => [])
        (buildPanLprefixLub _ (by
          intro _ _
          exact Or.inl (List.prefix_refl []))) := by
  classical
  have hforbidden : ¬ panHasForbiddenRun (hooksFor divergingEvaluate) :=
    divergenceBranch.1
  have hsuccessful : ¬ panHasSuccessfulRun (hooksFor divergingEvaluate) :=
    divergenceBranch.2
  simp only [panSemantics, panSemanticsWithLub, dif_neg hforbidden,
    dif_neg hsuccessful]
  congr 2

#guard sourceClockParity

def runChecks : IO Bool := do
  if sourceClockParity then
    IO.println "PASS panSem semantics source clock observations"
  else
    IO.println "FAIL panSem semantics source clock observations"
  IO.println "PASS panSem semantics source branch proofs"
  pure sourceClockParity

end Flapjack.Test.PanObservationalSemanticsParity
