import Flapjack.LoopCall

/-!
# Original-domain parity for `loop_call$comp`

`original*` observations below are taken from the checked-in HOL fixture
`scripts/hol-probes/loop_call_comp_probe.out`, generated from
`cakeml/pancake/loop_callScript.sml:18-92`.  The observations deliberately
cover the environment-sensitive call, assignment, location, load, primitive,
arithmetic, sequence, branch, loop, mark, FFI, and fallback equations.
-/

namespace Flapjack.Test.LoopCallParity

open Flapjack
open Flapjack.LoopCall

def sourceEnvironment : LocationEnv := [(2, 9)]
def sourceEnvironmentTwo : LocationEnv := [(1, 7), (2, 8)]

def isSkip : LoopProg α → Bool
  | .skip => true
  | _ => false

def isSeq : LoopProg α → Bool
  | .seq _ _ => true
  | _ => false

def isIte : LoopProg α → Bool
  | .ite _ _ _ _ _ _ => true
  | _ => false

def isLoop : LoopProg α → Bool
  | .loop _ _ _ => true
  | _ => false

def isMark : LoopProg α → Bool
  | .mark _ => true
  | _ => false

def callShape : LoopProg α → Option (Option Nat × List Nat)
  | .call _ target arguments _ => some (target, arguments)
  | _ => none

def compiledEnv (environment : LocationEnv) (program : LoopProg Nat) : LocationEnv :=
  (comp environment program).2

def compiledProgram (environment : LocationEnv) (program : LoopProg Nat) : LoopProg Nat :=
  (comp environment program).1

def probeSkip : LoopProg Nat := .skip
def probeCallDest : LoopProg Nat := .call none (some 3) [1, 2] none
def probeCallLast : LoopProg Nat := .call none none [1, 2] none
def probeCallEmpty : LoopProg Nat := .call none none [] none
def probeLocValue : LoopProg Nat := .locValue 1 7
def probeAssignVar : LoopProg Nat := .assign 1 (.var 2)
def probeAssignExpr : LoopProg Nat := .assign 1 (.const 9)
def probeShMem : LoopProg Nat := .shMem .load 1 (.const 0)
def probeLoad32 : LoopProg Nat := .load32 0 1
def probeLoadByte : LoopProg Nat := .loadByte 0 1
def probeSequence : LoopProg Nat :=
  .seq (.locValue 2 8) (.assign 3 (.var 2))
def probeIf : LoopProg Nat :=
  .ite .equal 0 (.reg 2) (.locValue 2 8) (.assign 3 (.var 2)) []
def probeLoop : LoopProg Nat := .loop [] (.locValue 2 8) []
def probeMark : LoopProg Nat := .mark (.locValue 2 8)
def probeFfi : LoopProg Nat := .ffi "host" 1 2 3 4 []
def probePrimitive : LoopProg Nat := .primitive [1] .addCarry [2, 3]
def probeLongMul : LoopProg Nat := .arith (.longMul 1 2 3 4)
def probeDiv : LoopProg Nat := .arith (.div 1 2 3)
def probeFallback : LoopProg Nat := .store (.const 0) 1

#guard isSkip (compiledProgram [] probeSkip)
#guard callShape (compiledProgram [] probeCallDest) == some (some 3, [1, 2])
#guard callShape (compiledProgram sourceEnvironment probeCallLast) ==
  some (some 9, [1])
#guard isSkip (compiledProgram [] probeCallEmpty)
#guard lookup 2 (compiledEnv sourceEnvironment probeCallLast) == none
#guard lookup 1 (compiledEnv [] probeLocValue) == some 7
#guard lookup 1 (compiledEnv [(2, 7)] probeAssignVar) == some 7
#guard lookup 1 (compiledEnv [(1, 7)] probeAssignVar) == none
#guard lookup 1 (compiledEnv [(1, 7)] probeAssignExpr) == none
#guard lookup 1 (compiledEnv [(1, 7)] probeShMem) == none
#guard lookup 1 (compiledEnv [(1, 7)] probeLoad32) == none
#guard lookup 1 (compiledEnv [] probeLoadByte) == none
#guard isSeq (compiledProgram [(1, 7)] probeSequence)
#guard isIte (compiledProgram [(1, 7)] probeIf)
#guard isLoop (compiledProgram [(1, 7)] probeLoop)
#guard lookup 2 (compiledEnv [(1, 7)] probeMark) == some 8
#guard lookup 1 (compiledEnv [(1, 7)] probeFfi) == none
#guard lookup 1 (compiledEnv sourceEnvironmentTwo probePrimitive) == none
#guard lookup 2 (compiledEnv sourceEnvironmentTwo probePrimitive) == some 8
#guard lookup 1 (compiledEnv sourceEnvironmentTwo probeLongMul) == none
#guard lookup 2 (compiledEnv sourceEnvironmentTwo probeLongMul) == none
#guard lookup 1 (compiledEnv [(1, 7)] probeDiv) == none
#guard lookup 1 (compiledEnv [(1, 7)] probeFallback) == some 7

def check (name : String) (actual expected : Bool) : IO Bool := do
  if actual == expected then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}: expected {expected}, got {actual}"
    pure false

def runChecks : IO Bool := do
  let results ← [
    check "loop_call skip" (isSkip (compiledProgram [] probeSkip)) true,
    check "loop_call call destination"
      (callShape (compiledProgram [] probeCallDest) == some (some 3, [1, 2])) true,
    check "loop_call call last argument"
      (callShape (compiledProgram sourceEnvironment probeCallLast) ==
        some (some 9, [1])) true,
    check "loop_call empty call" (isSkip (compiledProgram [] probeCallEmpty)) true,
    check "loop_call loc value"
      (lookup 1 (compiledEnv [] probeLocValue) == some 7) true,
    check "loop_call assign var copy"
      (lookup 1 (compiledEnv [(2, 7)] probeAssignVar) == some 7) true,
    check "loop_call shmem clears" 
      (lookup 1 (compiledEnv [(1, 7)] probeShMem) == none) true,
    check "loop_call sequence" (isSeq (compiledProgram [] probeSequence)) true,
    check "loop_call if" (isIte (compiledProgram [] probeIf)) true,
    check "loop_call loop" (isLoop (compiledProgram [] probeLoop)) true,
    check "loop_call mark" (lookup 2 (compiledEnv [(1, 7)] probeMark) == some 8) true,
    check "loop_call primitive" 
      (lookup 2 (compiledEnv sourceEnvironmentTwo probePrimitive) == some 8) true,
    check "loop_call arithmetic" 
      (lookup 1 (compiledEnv sourceEnvironmentTwo probeLongMul) == none) true,
    check "loop_call fallback" 
      (lookup 1 (compiledEnv [(1, 7)] probeFallback) == some 7) true ].mapM id
  pure (results.all id)

end Flapjack.Test.LoopCallParity
