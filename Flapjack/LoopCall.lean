import Flapjack.Loop

/-!
# Pancake `loop_call.comp`

This is the executable port of `cakeml/pancake/loop_callScript.sml:18-92`.
The environment is the source pass's `num |-> num` map, represented here by
an association list with first-match lookup and newest-entry insertion.  The
pass only carries location information through the cases where CakeML's
`comp_def` does so; all other forms return the source environment unchanged
or clear it exactly as the source equations specify.
-/

namespace Flapjack

namespace LoopCall

abbrev LocationEnv := List (Nat × Nat)

def lookup (name : Nat) : LocationEnv → Option Nat
  | [] => none
  | (candidate, location) :: entries =>
      if candidate = name then some location else lookup name entries

def insert (name location : Nat) (environment : LocationEnv) : LocationEnv :=
  (name, location) :: environment

def delete (name : Nat) : LocationEnv → LocationEnv
  | [] => []
  | (candidate, location) :: entries =>
      if candidate = name then delete name entries
      else (candidate, location) :: delete name entries

def listDelete (names : List Nat) (environment : LocationEnv) : LocationEnv :=
  names.foldl (fun environment name => delete name environment) environment

def splitLast : List α → Option (List α × α)
  | [] => none
  | value :: values =>
      match splitLast values with
      | none => some ([], value)
      | some (pre, lastValue) => some (value :: pre, lastValue)
termination_by values => sizeOf values

def compArith (environment : LocationEnv) : LoopArith → LocationEnv
  | .longMul sourceLeft sourceRight _ _
  | .longDiv sourceLeft sourceRight _ _ _ =>
      match lookup sourceLeft environment, lookup sourceRight environment with
      | none, none => environment
      | some _, none => delete sourceLeft environment
      | none, some _ => delete sourceRight environment
      | some _, some _ => delete sourceLeft (delete sourceRight environment)
  | .div destination _ _ =>
      match lookup destination environment with
      | none => environment
      | some _ => delete destination environment

def compCall (environment : LocationEnv)
    (returns : Option (List Nat × List Nat)) (target : Option Nat)
    (arguments : List Nat) (handler : Option (Nat × LoopProg α × LoopProg α × List Nat)) :
    LoopProg α × LocationEnv :=
  match target with
  | some _ => (.call returns target arguments handler, [])
  | none =>
      match splitLast arguments with
      | none => (.skip, [])
      | some (pre, lastValue) =>
          match lookup lastValue environment with
          | none => (.call returns none arguments handler, [])
          | some destination =>
              (.call returns (some destination) pre handler, [])

def comp : LocationEnv → LoopProg α → LoopProg α × LocationEnv
  | environment, .skip => (.skip, environment)
  | environment, .call returns target arguments handler =>
      compCall environment returns target arguments handler
  | environment, program@(.locValue destination source) =>
      (program, insert destination source environment)
  | environment, program@(.assign destination (.var source)) =>
      (program,
        match lookup destination environment, lookup source environment with
        | none, none => environment
        | some _, none => delete destination environment
        | _, some location => insert destination location environment)
  | environment, program@(.assign destination _) =>
      (program,
        match lookup destination environment with
        | none => environment
        | some _ => delete destination environment)
  | _, program@(.shMem _ _ _) => (program, [])
  | environment, program@(.load32 _ destination) =>
      (program,
        match lookup destination environment with
        | none => environment
        | some _ => delete destination environment)
  | environment, program@(.loadByte _ destination) =>
      (program,
        match lookup destination environment with
        | none => environment
        | some _ => delete destination environment)
  | environment, .seq first second =>
      let (compiledFirst, nextEnvironment) := comp environment first
      let (compiledSecond, _) := comp nextEnvironment second
      (.seq compiledFirst compiledSecond, [])
  | environment, .ite operator condition right thenBranch elseBranch live =>
      let (compiledThen, _) := comp environment thenBranch
      let (compiledElse, _) := comp environment elseBranch
      (.ite operator condition right compiledThen compiledElse live, [])
  | _, .loop liveIn body liveOut =>
      let (compiledBody, _) := comp [] body
      (.loop liveIn compiledBody liveOut, [])
  | environment, .mark body =>
      let (compiledBody, nextEnvironment) := comp environment body
      (.mark compiledBody, nextEnvironment)
  | _, program@(.ffi _ _ _ _ _ _) => (program, [])
  | _, program@.tick => (program, [])
  | _, program@(.raise _) => (program, [])
  | _, program@(.return _) => (program, [])
  | environment, program@(.primitive destinations _ _) =>
      (program, listDelete destinations environment)
  | environment, program@(.arith operation) =>
      (program, compArith environment operation)
  | environment, program => (program, environment)
termination_by _ program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

end LoopCall

end Flapjack
