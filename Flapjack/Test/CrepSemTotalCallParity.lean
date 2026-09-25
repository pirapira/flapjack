import Flapjack.Pancake.Semantics.CrepSem.TotalEval

/-! Direct regression cases for the supported source-code-map Call fragment.
    Oracle rows come from crep_total_call_eval_probeScript.sml. -/

namespace Flapjack.Test.CrepSemTotalCallParity

open Flapjack

def callState (clock : Nat) : CrepHolState (BitVec 64) Unit :=
  { locals := fun name => if name == 0 then some (.word 7)
      else if name == 1 then some (.word 3) else none
    globals := fun _ => none
    code := fun function =>
      if function == "id" then some ([0], CrepProg.return [.var 0]) else none
    memory := fun _ => .word 0
    memaddrs := fun _ => false
    shMemaddrs := fun _ => false
    clock := clock
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 0
    topAddress := 100 }

def callOracleRowsMatch : Bool :=
  let state := callState 5
  let zero := callState 0
  let success := match evalCrepClockProg (.call none "id" [.const 9]) state with
    | (some (.return [.word 9]), post) =>
        post.clock == 4 && post.locals 0 == none &&
          (match post.code "id" with
          | some ([0], .return [.var 0]) => true
          | _ => false)
    | _ => false
  let destinations := match evalCrepClockProg
      (.call (some [1]) "id" [.const 9]) state with
    | (none, post) => post.clock == 4 && post.locals 0 == some (.word 7) &&
        post.locals 1 == some (.word 9)
    | _ => false
  let missing := match evalCrepClockProg (.call none "missing" [.const 9]) state with
    | (some .error, post) => post.clock == 5 && post.locals 0 == state.locals 0
    | _ => false
  let arity := match evalCrepClockProg (.call none "id" []) state with
    | (some .error, post) => post.clock == 5 && post.locals 1 == state.locals 1
    | _ => false
  let timeout := match evalCrepClockProg (.call none "id" [.const 9]) zero with
    | (some .timeOut, post) => post.clock == 0 && post.locals 0 == none
    | _ => false
  success && destinations && missing && arity && timeout

#guard callOracleRowsMatch

def runChecks : IO Bool := do
  if callOracleRowsMatch then
    IO.println "PASS total Crep Call evaluates state-owned code entries and matches direct HOL rows"
  else
    IO.println "FAIL total Crep Call evaluates state-owned code entries and matches direct HOL rows"
  pure callOracleRowsMatch

end Flapjack.Test.CrepSemTotalCallParity
