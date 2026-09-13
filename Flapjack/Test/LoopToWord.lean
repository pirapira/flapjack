import Flapjack.LoopToWord

/-!
# Loop-to-word context lookup parity tests

These regressions exercise the ports of `find_var_def`, `find_reg_imm_def` and
`make_ctxt_def` from `cakeml/pancake/loop_to_wordScript.sml`.  The expected
values are the ones the original script computes: a missing variable maps to
`0`, `make_ctxt` starts at register `2` and advances by `2`, and the register
case of `find_reg_imm` is routed through `find_var`.
-/

namespace Flapjack.Test.LoopToWord

open Flapjack Flapjack.LoopToWord

/-! Independent transcription of the script's `lookup`-then-`NONE => 0` rule,
via first-match search, used to cross-check the port. -/
def referenceFindVar (context : List (Nat × Nat)) (name : Nat) : Nat :=
  match context.find? (fun pair => pair.1 = name) with
  | none => 0
  | some pair => pair.2

/-! Independent transcription of `make_ctxt` as index arithmetic. -/
def referenceMakeCtxt (next : Nat) (variables : List Nat)
    (context : List (Nat × Nat)) : List (Nat × Nat) :=
  (variables.zip (List.range variables.length)).foldl
    (fun acc (pair : Nat × Nat) => (pair.1, next + 2 * pair.2) :: acc)
    context

#guard findVar [] 0 == 0
#guard findVar [] 99 == 0
#guard findVar [(3, 7)] 3 == 7
#guard findVar [(3, 7)] 4 == 0
#guard findVar (makeCtxt 2 [10, 11, 12] []) 10 == 2
#guard findVar (makeCtxt 2 [10, 11, 12] []) 11 == 4
#guard findVar (makeCtxt 2 [10, 11, 12] []) 12 == 6
#guard findVar (makeCtxt 2 [10, 11, 12] []) 99 == 0

example : findRegImm [] (.imm 5 : RegImm Nat) = .imm 5 := rfl
example : findRegImm [] (.reg 11 : RegImm Nat) = .reg 0 := rfl
example : findRegImm (makeCtxt 2 [10, 11, 12] []) (.reg 11 : RegImm Nat) =
    .reg 4 := rfl

def contexts : List (List (Nat × Nat)) :=
  [ [], [(3, 7)], [(10, 2), (11, 4), (12, 6)],
    (makeCtxt 2 [1, 2, 3] []) ]

def variables : List Nat := [0, 1, 2, 3, 7, 10, 11, 12, 99]

def runChecks : IO Bool := do
  let mut ok := true
  for context in contexts do
    for name in variables do
      if findVar context name != referenceFindVar context name then
        IO.println s!"FAIL LoopToWord.findVar {repr context} {name}"
        ok := false
  for count in [0, 1, 2, 5] do
    let sample := (List.range count).map (fun index => 100 + index)
    if makeCtxt 2 sample [] != referenceMakeCtxt 2 sample [] then
      IO.println s!"FAIL LoopToWord.makeCtxt {repr sample}"
      ok := false
  if ok then
    IO.println "PASS LoopToWord find_var/find_reg_imm/make_ctxt parity"
  pure ok

end Flapjack.Test.LoopToWord
