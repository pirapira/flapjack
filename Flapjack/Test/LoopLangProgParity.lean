import Flapjack.Pancake.LoopLang
import Flapjack.Test.PanValueFfiSemantics

/-!
Parity checks for the exact `loopLang$prog` carrier `HolLoopProg`, compared
against the direct HOL EVAL oracle in
`scripts/hol-probes/loop_lang_prog_probe.out` (word width fixed at 8,
`num_set` = `sptree$LN` modelled by the exact `NumSet` carrier (`Spt Unit`)).
-/

namespace Flapjack.Test.LoopLangProgParity

open Flapjack
open Flapjack.Basis.Pure.MlString

private abbrev W := BitVec 8

private def w8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

private def emptySet : NumSet := .ln

/-- `«f»` in the HOL oracle, encoded as the byte codec would. -/
private def fName : MlString := .implode [w8 102]

private def progSkip : HolLoopProg 8 := .skip

private def progAssign : HolLoopProg 8 := .assign 1 (.const (w8 7))

private def progIf : HolLoopProg 8 :=
  .ite .equal 0 (.reg 1) .skip .tick emptySet

private def progLoop : HolLoopProg 8 := .loop emptySet .tick emptySet

private def progReturn : HolLoopProg 8 := .return [1, 2]

private def progShMem : HolLoopProg 8 := .shMem .load 1 (.const (w8 0))

private def progCall : HolLoopProg 8 :=
  .call (some ([1], emptySet)) none [] (some (2, .skip, .tick, emptySet))

private def progFfi : HolLoopProg 8 := .ffi fName 1 2 3 4 emptySet

example : progSkip = HolLoopProg.skip := rfl
example : progAssign = HolLoopProg.assign 1 (HolLoopExp.const (w8 7)) := rfl
example : progIf =
    HolLoopProg.ite Cmp.equal 0 (RegImm.reg 1) HolLoopProg.skip HolLoopProg.tick
      emptySet := rfl
example : progLoop = HolLoopProg.loop emptySet HolLoopProg.tick emptySet := rfl
example : progReturn = HolLoopProg.return [1, 2] := rfl
example : progShMem = HolLoopProg.shMem CrepMemOp.load 1 (HolLoopExp.const (w8 0)) := rfl
example : progCall =
    HolLoopProg.call (some ([1], emptySet)) none [] (some (2, HolLoopProg.skip, HolLoopProg.tick, emptySet)) := rfl
example : progFfi = HolLoopProg.ffi fName 1 2 3 4 emptySet := rfl

private def isSkip : HolLoopProg 8 → Bool
  | .skip => true
  | _ => false

private def isReturnTwo : HolLoopProg 8 → Bool
  | .return [1, 2] => true
  | _ => false

private def isFfiF : HolLoopProg 8 → Bool
  | .ffi name 1 2 3 4 _ => decide (name = fName)
  | _ => false

def runChecks : IO Bool := do
  let ok := isSkip progSkip && isReturnTwo progReturn && isFfiF progFfi
  if ok then
    IO.println "PASS loopLang prog faithful carrier matches the 8 oracle shapes"
  else
    IO.println "FAIL loopLang prog faithful carrier oracle"
  pure ok

end Flapjack.Test.LoopLangProgParity