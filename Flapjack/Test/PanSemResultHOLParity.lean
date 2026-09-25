/-
Lean parity fixtures for the exact HOL `panSem$result` carrier (`ResultHOL`).

The rows mirror `scripts/hol-probes/pan_sem_result_probe.out`: each HOL
constructor shape appears once, plus a distinctness row. `ResultHOL` carries
`ValueHOL`/`mlstring`/`final_event` payloads that have no `DecidableEq`, so the
fixtures use a constructor tag/projection encoding instead of `==`.
-/

import Flapjack.Pancake.Semantics.PanSem.ResultHOL

namespace Flapjack.Test.PanSemResultHOLParity

open Flapjack

/-- Constructor tag matching the HOL `result` constructor order. -/
private def tag : ResultHOL 8 → Nat
  | .error => 0
  | .timeOut => 1
  | .break => 2
  | .continue => 3
  | .return _ => 4
  | .exception _ _ => 5
  | .finalFfi _ => 6

private def mlE : Flapjack.Basis.Pure.MlString.MlString :=
  Flapjack.Basis.Pure.MlString.ofString "E"

private def valWord7 : ValueHOL 8 := .val (.word (BitVec.ofNat 8 7))

private def finalEvent : HolFinalEvent :=
  { name := .extCall mlE, configuration := [], bytes := [], outcome := .failed }

private def resultErr : ResultHOL 8 := .error
private def resultTimeOut : ResultHOL 8 := .timeOut
private def resultBreak : ResultHOL 8 := .break
private def resultContinue : ResultHOL 8 := .continue
private def resultReturn : ResultHOL 8 := .return valWord7
private def resultException : ResultHOL 8 := .exception mlE valWord7
private def resultFinalFfi : ResultHOL 8 := .finalFfi finalEvent

/-- Payload of a `Return`, defaulted for the other constructors. -/
private def returnPayload : ResultHOL 8 → ValueHOL 8
  | .return value => value
  | _ => .val (.word 0)

/-- Exception identifier of an `Exception`, defaulted for the other constructors. -/
private def exceptionName : ResultHOL 8 → Flapjack.Basis.Pure.MlString.MlString
  | .exception name _ => name
  | _ => .implode []

/-- FFI outcome of a `FinalFFI`, defaulted for the other constructors. -/
private def finalOutcome : ResultHOL 8 → HolFfiOutcome
  | .finalFfi event => event.outcome
  | _ => .failed

-- Oracle rows `res_error` .. `res_finalffi`.
example : tag resultErr = 0 := rfl
example : tag resultTimeOut = 1 := rfl
example : tag resultBreak = 2 := rfl
example : tag resultContinue = 3 := rfl
example : tag resultReturn = 4 := rfl
example : tag resultException = 5 := rfl
example : tag resultFinalFfi = 6 := rfl

-- Payload shape rows (`Return (ValWord 7w)`, `Exception «E» (ValWord 7w)`,
-- `FinalFFI (Final_event (ExtCall «E») [] [] FFI_failed)`).
example : returnPayload resultReturn = valWord7 := rfl
example : exceptionName resultException = mlE := rfl
example : finalOutcome resultFinalFfi = .failed := rfl

-- Oracle row `res_distinct`.
example : (tag resultTimeOut == 1 && tag resultBreak == 2) = true := rfl

/-- `ValueHOL` has no `BEq`, so recognise the `ValWord 7w` payload structurally. -/
private def isValWord7 : ValueHOL 8 → Bool
  | .val (.word w) => w == BitVec.ofNat 8 7
  | _ => false

private def resultGuard : Bool :=
  (tag resultErr == 0) && (tag resultTimeOut == 1) && (tag resultBreak == 2) &&
  (tag resultContinue == 3) && (tag resultReturn == 4) &&
  (tag resultException == 5) && (tag resultFinalFfi == 6) &&
  isValWord7 (returnPayload resultReturn) && (exceptionName resultException == mlE) &&
  (finalOutcome resultFinalFfi == .failed)

#eval resultGuard
#guard resultGuard

def runChecks : IO Bool := do
  if resultGuard then
    IO.println "PASS panSem result exact carrier matches all 8 oracle rows"
    pure true
  else
    IO.println "FAIL panSem result exact carrier"
    pure false

end Flapjack.Test.PanSemResultHOLParity