import Flapjack.LoopAnalysis

/-!
# Original-domain parity for `acc_vars`

`loopAccVars` is the Lean counterpart of
`cakeml/pancake/loopLangScript.sml:117-158`.  The checked-in expected values
come from `loop_lang_acc_vars_probeScript.sml`, so these tests expose the
source behavior that allocation analysis must follow: expression operands,
stores, returns, call arguments, and FFI operands are not accumulated by
`acc_vars`.
-/

namespace Flapjack.Test.LoopAccVarsParity

open Flapjack

def originalSkip : List Nat := []
def originalAssign : List Nat := [7]
def originalReturn : List Nat := []
def originalStore : List Nat := []
def originalLongDiv : List Nat := [1, 2]
def originalCallNone : List Nat := []

def probeSkip : LoopProg Nat := .skip
def probeAssign : LoopProg Nat := .assign 7 (.const 1)
def probeReturn : LoopProg Nat := .return [7, 8]
def probeStore : LoopProg Nat := .store (.var 4) 7
def probeLongDiv : LoopProg Nat := .arith (.longDiv 1 2 3 4 5)
def probeCallNone : LoopProg Nat := .call none (some 3) [4, 5] none
def probeIf : LoopProg Nat :=
  .ite .less 8 (.reg 9) (.assign 11 (.const 1)) (.assign 12 (.const 2)) []
def probeReverseSeq : LoopProg Nat :=
  .seq (.assign 5 (.const 1)) (.assign 2 (.const 2))

#guard loopAccVars probeSkip [] == originalSkip
#guard loopAccVars probeAssign [] == originalAssign
#guard loopAccVars probeReturn [] == originalReturn
#guard loopAccVars probeStore [] == originalStore
#guard loopAccVars probeLongDiv [] == originalLongDiv
#guard loopAccVars probeCallNone [] == originalCallNone
#guard loopAccVars probeIf [] == [11, 12]
#guard loopAccVars probeReverseSeq [] == [2, 5]

def check (name : String) (actual expected : List Nat) : IO Bool := do
  if actual == expected then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}: expected {repr expected}, got {repr actual}"
    pure false

def runChecks : IO Bool := do
  let results ← [
    check "acc_vars skip" (loopAccVars probeSkip []) originalSkip,
    check "acc_vars assign" (loopAccVars probeAssign []) originalAssign,
    check "acc_vars ignores return values"
      (loopAccVars probeReturn []) originalReturn,
    check "acc_vars ignores store operands"
      (loopAccVars probeStore []) originalStore,
    check "acc_vars long division" (loopAccVars probeLongDiv []) originalLongDiv,
    check "acc_vars ignores call arguments"
      (loopAccVars probeCallNone []) originalCallNone,
    check "acc_vars ignores if condition operands"
      (loopAccVars probeIf []) [11, 12],
    check "acc_vars exposes num_set order"
      (loopAccVars probeReverseSeq []) [2, 5] ].mapM id
  pure (results.all id)

end Flapjack.Test.LoopAccVarsParity
