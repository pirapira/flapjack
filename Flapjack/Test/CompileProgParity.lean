import Flapjack.Pipeline

namespace Flapjack.Test.CompileProgParity

open Flapjack

def compileProgProbeContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

def compileProgProbeDecls : List (Decl Nat) :=
  [.function
     { name := "leaf", inline := true, exported := false, params := [],
       body := .return (.const 7), returnShape := .one },
   .function
     { name := "mid", inline := true, exported := false, params := [],
       body := .call none "leaf" [], returnShape := .one },
   .function
     { name := "main", inline := false, exported := true, params := [],
       body := .call none "mid" [], returnShape := .one }]

/-! The fixture is the direct HOL evaluation of
    `pan_to_crep$compile_prog` on the same inline callee/caller pair. -/
theorem compile_prog_inline_call_parity :
    compileProgToCrep compileProgProbeContext compileProgProbeDecls =
      [{ name := "leaf", params := [], body := .return [.const 7],
         returnShape := .one },
       { name := "mid", params := [],
         body := .seq .tick (.return [.const 7]), returnShape := .one },
       { name := "main", params := [],
         body := .seq .tick (.seq .tick (.return [.const 7])), returnShape := .one }] := by
  simp [compileProgToCrep, pipelineInlineNames, compileToCrep,
    compileFunctionsSource, compileFunDeclSource, compileParamVars,
    functionInfos, compileProgProbeContext, compileProgProbeDecls,
    compileProg, compileExp, compileArgs,
    crepInlineTopRecursiveByNames, crepInlineTopRecursive,
    crepInlineFunctionsRecursive, crepInlineActiveNames,
    crepInlineProgRecursive, crepInlineLookup, crepInlineCallBody,
    crepInlineTail, crepArgLoad, crepInlineTmpNames, crepUnreachElim,
    nestedDecs]

def parityGuard : Bool :=
  match compileProgToCrep compileProgProbeContext compileProgProbeDecls with
  | [{ name := "leaf", params := [], body := .return [.const 7],
         returnShape := .one },
     { name := "mid", params := [],
       body := .seq .tick (.return [.const 7]), returnShape := .one },
     { name := "main", params := [],
       body := .seq .tick (.seq .tick (.return [.const 7])), returnShape := .one }] => true
  | _ => false

#eval parityGuard
#guard parityGuard

/-! Cake's `crep_inline` prunes an inline callee at its first terminal
    statement before splicing it into the caller.  The assignment after the
    return is deliberately unreachable and must not survive the inline. -/
def compileProgUnreachableInlineEntries : List (CrepInlineEntry Nat) :=
  [("callee", ([],
    .seq (.return [.const 7]) (.assign 99 (.const 42))))]

def compileProgUnreachableInlineResult : CrepProg Nat :=
  crepInlineProgRecursive compileProgUnreachableInlineEntries
    (crepInlineActiveNames compileProgUnreachableInlineEntries)
    (.call none "callee" [])

def compileProgUnreachableInlineGuard : Bool :=
  match compileProgUnreachableInlineResult with
  | .seq .tick (.return [.const 7]) => true
  | _ => false

#guard compileProgUnreachableInlineGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS compile_prog inline-call source parity"
  else
    IO.println "FAIL compile_prog parity"
  if compileProgUnreachableInlineGuard then
    IO.println "PASS compile_prog unreach-before-inline parity"
  else
    IO.println "FAIL compile_prog unreach-before-inline parity"
  pure (parityGuard && compileProgUnreachableInlineGuard)

end Flapjack.Test.CompileProgParity
