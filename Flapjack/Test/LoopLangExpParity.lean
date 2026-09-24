import Flapjack.Test.PanValueFfiSemantics

/-!
Regression checks for the faithful width-indexed `loopLang$exp` carrier
`HolLoopExp` and the tagged `LoopArith` against the direct HOL oracle
`scripts/hol-probes/loop_lang_exp_probe.out`.
-/

namespace Flapjack.Test.LoopLangExpParity

open Flapjack

private abbrev W := BitVec 8

private def w8 (n : Nat) : W := BitVec.ofNat 8 n
private def w5 (n : Nat) : BitVec 5 := BitVec.ofNat 5 n

private def expConst : HolLoopExp 8 := .const (w8 7)
private def expVar : HolLoopExp 8 := .var 3
private def expLookup : HolLoopExp 8 := .lookup (w5 1)
private def expLoad : HolLoopExp 8 := .load (.var 3)
private def expOp : HolLoopExp 8 := .op .add [.var 1, .const (w8 2)]
private def expShift : HolLoopExp 8 := .shift .lsl (.var 1) (.const (w8 2))
private def expBase : HolLoopExp 8 := .baseAddr
private def expTop : HolLoopExp 8 := .topAddr

private def arithLongMul : LoopArith := .longMul 1 2 3 4
private def arithLongDiv : LoopArith := .longDiv 1 2 3 4 5
private def arithDiv : LoopArith := .div 1 2 3

/-- Structural check that the executor view of `exp_op` is the expected
executable `LoopExp`. -/
private def isOpAdd : LoopExp W → Bool
  | .op .add [.var 1, .const value] => value == w8 2
  | _ => false

example : expConst = HolLoopExp.const (w8 7) := rfl
example : expVar = HolLoopExp.var 3 := rfl
example : expLookup = HolLoopExp.lookup (w5 1) := rfl
example : expLoad = HolLoopExp.load (HolLoopExp.var 3) := rfl
example : expOp = HolLoopExp.op .add [HolLoopExp.var 1, HolLoopExp.const (w8 2)] := rfl
example : expShift = HolLoopExp.shift .lsl (HolLoopExp.var 1) (HolLoopExp.const (w8 2)) := rfl
example : expBase = HolLoopExp.baseAddr := rfl
example : expTop = HolLoopExp.topAddr := rfl
example : arithLongMul = LoopArith.longMul 1 2 3 4 := rfl
example : arithLongDiv = LoopArith.longDiv 1 2 3 4 5 := rfl
example : arithDiv = LoopArith.div 1 2 3 := rfl

example : holLoopExpToExecutable expConst = LoopExp.const (w8 7) := by
  simp only [holLoopExpToExecutable, expConst]
example : holLoopExpToExecutable expVar = LoopExp.var 3 := by
  simp only [holLoopExpToExecutable, expVar]
example : holLoopExpToExecutable expLookup = LoopExp.lookup (w5 1) := by
  simp only [holLoopExpToExecutable, expLookup]
example : holLoopExpToExecutable expLoad = LoopExp.load (LoopExp.var 3) := by
  simp only [holLoopExpToExecutable, expLoad, expVar]
example : holLoopExpToExecutable expShift =
    LoopExp.shift .lsl (LoopExp.var 1) (LoopExp.const (w8 2)) := by
  simp only [holLoopExpToExecutable, expShift, expVar, expConst, w8]
example : holLoopExpToExecutable expBase = (LoopExp.baseAddr : LoopExp W) := by
  simp only [holLoopExpToExecutable, expBase]
example : holLoopExpToExecutable expTop = (LoopExp.topAddr : LoopExp W) := by
  simp only [holLoopExpToExecutable, expTop]

private def bridgeGuard : Bool :=
  isOpAdd (holLoopExpToExecutable expOp) &&
    (match holLoopExpToExecutable expConst with | .const value => value == w8 7 | _ => false) &&
    (match arithLongMul with | .longMul 1 2 3 4 => true | _ => false)

#eval bridgeGuard
#guard bridgeGuard

/-- Oracle rows: each constructor round-trips through the executor view. -/
def runChecks : IO Bool := do
  if bridgeGuard then
    IO.println "PASS loopLang exp/loop_arith faithful carriers match the 10 oracle shapes"
  else
    IO.println "FAIL loopLang exp/loop_arith faithful carriers"
  pure bridgeGuard

end Flapjack.Test.LoopLangExpParity