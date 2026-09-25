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

def callStateWith (clock : Nat) (function : FunName) (parameters : List Nat)
    (body : CrepProg (BitVec 64)) : CrepHolState (BitVec 64) Unit :=
  { callState clock with
    code := fun name =>
      if name == function then some (parameters, body) else none }

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
  let normal := match evalCrepClockProg (.call none "worker" [])
      (callStateWith 5 "worker" [] .skip) with
    | (some .error, post) => post.clock == 4 && post.locals 0 == none
    | _ => false
  let breaking := match evalCrepClockProg (.call none "worker" [])
      (callStateWith 5 "worker" [] (.break 0)) with
    | (some .error, post) => post.clock == 4 && post.locals 0 == none
    | _ => false
  let continuing := match evalCrepClockProg (.call none "worker" [])
      (callStateWith 5 "worker" [] (.continue 0)) with
    | (some .error, post) => post.clock == 4 && post.locals 0 == none
    | _ => false
  let exception := match evalCrepClockProg (.call none "worker" [])
      (callStateWith 5 "worker" [] (.raise (BitVec.ofNat 64 3))) with
    | (some (.exception 3), post) => post.clock == 4 && post.locals 0 == none
    | _ => false
  let returnArity := match evalCrepClockProg
      (.call (some [1, 2]) "ret" [])
      (callStateWith 5 "ret" [] (.return [.const 9])) with
    | (some .error, post) => post.clock == 4 && post.locals 0 == none
    | _ => false
  let duplicateDestinations := match evalCrepClockProg
      (.call (some [1, 1]) "id" [.const 9]) state with
    | (some .error, post) => post.clock == 5 && post.locals 0 == state.locals 0
    | _ => false
  let missingDestination := match evalCrepClockProg
      (.call (some [9]) "id" [.const 9]) state with
    | (some .error, post) => post.clock == 4 && post.locals 0 == none
    | _ => false
  success && destinations && missing && arity && timeout && normal &&
    breaking && continuing && exception && returnArity &&
    duplicateDestinations && missingDestination

#guard callOracleRowsMatch

def runChecks : IO Bool := do
  if callOracleRowsMatch then
    IO.println "PASS total Crep Call evaluates state-owned code entries and matches direct HOL rows"
  else
    IO.println "FAIL total Crep Call evaluates state-owned code entries and matches direct HOL rows"
  pure callOracleRowsMatch

end Flapjack.Test.CrepSemTotalCallParity
