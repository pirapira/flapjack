import Flapjack.LoopToWord
import Flapjack.Test.LoopToWordFixture

/-!
# Loop-to-word context lookup parity tests

These regressions exercise the ports of `find_var_def`, `find_reg_imm_def` and
`make_ctxt_def` from `cakeml/pancake/loop_to_wordScript.sml`.  The expected
values come from `Flapjack.Test.LoopToWordFixture`, which records the output of
the original definitions via HOL4 `EVAL` (`scripts/probe-loop-to-word.sml`).
No second Lean implementation is used as an oracle.
-/

namespace Flapjack.Test.LoopToWord

open Flapjack Flapjack.LoopToWord
open Flapjack.Test.LoopToWordFixture

#guard findVarCases.all (fun (context, name, expected) =>
  findVar context name == expected)

#guard makeCtxtCases.all (fun (next, variables, name, expected) =>
  findVar (makeCtxt next variables []) name == expected)

#guard findRegImmRegCases.all (fun (context, name, expected) =>
  findRegImm context (.reg name : RegImm Nat) == .reg expected)

#guard findRegImmImmCases.all (fun value =>
  findRegImm [] (.imm value : RegImm Nat) == .imm value)

def runChecks : IO Bool := do
  let mut ok := true
  for (context, name, expected) in findVarCases do
    let actual := findVar context name
    if actual != expected then
      IO.println s!"FAIL LoopToWord.findVar {repr context} {name} = {actual}, expected {expected}"
      ok := false
  for (next, variables, name, expected) in makeCtxtCases do
    let actual := findVar (makeCtxt next variables []) name
    if actual != expected then
      IO.println s!"FAIL LoopToWord.makeCtxt {next} {repr variables} {name} = {actual}, expected {expected}"
      ok := false
  for (context, name, expected) in findRegImmRegCases do
    if findRegImm context (.reg name : RegImm Nat) != (.reg expected : RegImm Nat) then
      IO.println s!"FAIL LoopToWord.findRegImmReg {repr context} {name}"
      ok := false
  for value in findRegImmImmCases do
    if findRegImm [] (.imm value : RegImm Nat) != (.imm value : RegImm Nat) then
      IO.println s!"FAIL LoopToWord.findRegImmImm {value}"
      ok := false
  if ok then
    IO.println "PASS LoopToWord find_var/find_reg_imm/make_ctxt original-parity"
  pure ok

end Flapjack.Test.LoopToWord
