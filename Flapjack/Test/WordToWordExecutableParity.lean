import Flapjack.Compiler.Backend.WordToWord.ExecutableCompile
import Flapjack.Test.WordInstSelectExactParity
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec

/-! Original full native WordToWord EVAL regressions. Complete expected programs
are transcribed from word_to_word_executable_probe.out, never derived from Lean
compilation. Runtime checks reject codec failures and compare full production
program observations plus function name and arity. Oracle remainder checks
observe every canonical tree through its full constructor representation. -/
namespace Flapjack.Test.WordToWordExecutableParity
open Flapjack Flapjack.Compiler.Backend.WordToWord
abbrev P := WordLangProgHOL (BitVec 64)
def cfg := { WordInstSelectExactParity.cfg with regCount := 32, avoidRegs := [0,2,3,4,31] }

private def input_skip : P := .skip
private def expected_skip : P := .skip

private def input_return : P := .return 0 [0]
private def expected_return : P := .seq (.move 1 [(2,0),(0,0)]) (.return 0 [2])

private def input_assign_return : P := .seq (.assign 2 (.op .add [.var 0,.const 7])) (.return 2 [2])
private def expected_assign_return : P := .seq (.move 1 [(0,0)]) (.seq (.inst (.arith (.binop .add 0 0 (.imm 7)))) (.seq (.move 0 [(2,0)]) (.return 0 [2])))

private def input_must_terminate : P := .mustTerminate (.return 0 [0])
private def expected_must_terminate : P := .seq (.move 1 [(0,0)]) (.seq (.move 0 [(2,0)]) (.return 0 [2]))

private def input_tail_call : P := .call none (some 9) [0] none
private def expected_tail_call : P := .seq (.move 1 [(0,0)]) (.call none (some 9) [0] none)

private def input_branch : P := .ite .equal 0 (.imm 0) (.return 0 [0]) (.raise 0)
private def expected_branch : P := .seq (.move 1 [(0,0)]) (.ite .equal 0 (.imm 0) (.seq (.move 0 [(2,0)]) (.return 0 [2])) (.seq (.move 1 [(2,0)]) (.raise 2)))

private def check (alg : Nat) (input expected : P) : Bool :=
  let (name, arity, actual) := fullCompileSingleExecutable false 22 alg cfg ((7,1,input),none)
  name == 7 && arity == 1 &&
    match wordLangProgFromHOL actual, wordLangProgFromHOL expected with
    | some a, some e => reprStr a == reprStr e
    | _, _ => false

private def observePrograms (ps : List (Nat × Nat × P)) : Option String := do
  let observed ← ps.mapM fun (n,a,p) => do
    let body ← wordLangProgFromHOL p
    pure (n,a,reprStr body)
  pure (reprStr observed)

private def checkPrograms (actual expected : List (Nat × Nat × P)) : Bool :=
  match observePrograms actual, observePrograms expected with
  | some a, some e => a == e
  | _, _ => false

def runChecks : IO Bool := do
  unless check 0 input_skip expected_skip do
    throw (IO.userError "original WordToWord skip_alg0 mismatch")
  unless check 2 input_skip expected_skip do
    throw (IO.userError "original WordToWord skip_alg2 mismatch")
  unless check 0 input_return expected_return do
    throw (IO.userError "original WordToWord return_alg0 mismatch")
  unless check 2 input_return expected_return do
    throw (IO.userError "original WordToWord return_alg2 mismatch")
  unless check 0 input_assign_return expected_assign_return do
    throw (IO.userError "original WordToWord assign_return_alg0 mismatch")
  unless check 2 input_assign_return expected_assign_return do
    throw (IO.userError "original WordToWord assign_return_alg2 mismatch")
  unless check 0 input_must_terminate expected_must_terminate do
    throw (IO.userError "original WordToWord must_terminate_alg0 mismatch")
  unless check 2 input_must_terminate expected_must_terminate do
    throw (IO.userError "original WordToWord must_terminate_alg2 mismatch")
  unless check 0 input_tail_call expected_tail_call do
    throw (IO.userError "original WordToWord tail_call_alg0 mismatch")
  unless check 2 input_tail_call expected_tail_call do
    throw (IO.userError "original WordToWord tail_call_alg2 mismatch")
  unless check 0 input_branch expected_branch do
    throw (IO.userError "original WordToWord branch_alg0 mismatch")
  unless check 2 input_branch expected_branch do
    throw (IO.userError "original WordToWord branch_alg2 mismatch")
  let conf : Config := ⟨0, []⟩
  unless (compileExecutable conf cfg []).1.isEmpty && (compileExecutable conf cfg []).2.isEmpty do
    throw (IO.userError "original WordToWord empty mismatch")
  let (col, ps) := compileExecutable ⟨0,[none,some .ln]⟩ cfg [(7,0,.skip)]
  unless reprStr col == reprStr ([some (Spt.ln : Spt Nat)]) && checkPrograms ps [(7,0,.skip)] do
    throw (IO.userError "original WordToWord oracle remainder mismatch")
  let (col, ps) := compileExecutable ⟨0,[some .ln]⟩ cfg [(7,0,.skip),(9,0,.skip)]
  unless col.isEmpty && checkPrograms ps [(7,0,.skip),(9,0,.skip)] do
    throw (IO.userError "original WordToWord short oracle mismatch")
  IO.println "PASS executable full native WordToWord: 12 body and 3 oracle cases"
  return true
end Flapjack.Test.WordToWordExecutableParity
