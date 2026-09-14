import Flapjack.Compile

/-!
# Original-domain parity for `pan_to_crep$compile` (`compile_def`)

The expected cases come from the direct HOL-EVAL fixture
`scripts/hol-probes/compile_def_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:139-305`.
-/

namespace Flapjack.Test.CompileDefParity

open Flapjack

def context : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 1 }

def isSkip : CrepProg Nat → Bool
  | .skip => true
  | _ => false

def isReturnSeven : CrepProg Nat → Bool
  | .return [.const 7] => true
  | _ => false

def isBreak : CrepProg Nat → Bool
  | .break 0 => true
  | _ => false

def isContinue : CrepProg Nat → Bool
  | .continue 0 => true
  | _ => false

def isSeqSkipTick : CrepProg Nat → Bool
  | .seq .skip .tick => true
  | _ => false

def parityGuard : Bool :=
  isSkip (compileProg context (.skip : Prog Nat)) &&
  isReturnSeven (compileProg context (.return (.const 7))) &&
  isBreak (compileProg context (.break : Prog Nat)) &&
  isContinue (compileProg context (.continue : Prog Nat)) &&
  isSeqSkipTick (compileProg context (.seq .skip (.tick : Prog Nat)))

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS compile_def skip/return/break/continue/seq parity"
  else
    IO.println "FAIL compile_def parity"
  pure parityGuard

end Flapjack.Test.CompileDefParity
