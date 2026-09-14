import Flapjack.Test.CrepeSemantics

/-!
# Original-domain parity for `crepSem.lookup_code_def`

The direct HOL fixture in `scripts/hol-probes/crep_lookup_code_probe.out` is
generated from `cakeml/pancake/semantics/crepSemScript.sml:76-84`.  The Lean
checks exercise valid binding, arity failure, duplicate-parameter failure,
and missing-function failure in `lookupCrepCode`.
-/

namespace Flapjack.Test.CrepLookupCodeParity

open Flapjack

def validBinding : Bool :=
  crepeLookupValid.map (fun result => result.2 1) == some (some 7)

def missingArity : Bool :=
  (lookupCrepCode "id" [] crepeLookupFunctions).isNone

def duplicateParameters : Bool :=
  (lookupCrepCode "duplicate" [7, 8] crepeLookupDuplicateFunctions).isNone

def missingFunction : Bool :=
  (lookupCrepCode "missing" [7] crepeLookupFunctions).isNone

#guard validBinding
#guard missingArity
#guard duplicateParameters
#guard missingFunction

def runChecks : IO Bool := do
  if validBinding then IO.println "PASS crep lookup_code valid binding" else
    IO.println "FAIL crep lookup_code valid binding"
  if missingArity then IO.println "PASS crep lookup_code arity failure" else
    IO.println "FAIL crep lookup_code arity failure"
  if duplicateParameters then
    IO.println "PASS crep lookup_code duplicate failure"
  else IO.println "FAIL crep lookup_code duplicate failure"
  if missingFunction then IO.println "PASS crep lookup_code missing failure" else
    IO.println "FAIL crep lookup_code missing failure"
  pure (validBinding && missingArity && duplicateParameters && missingFunction)

end Flapjack.Test.CrepLookupCodeParity
