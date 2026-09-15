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

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS compile_prog inline-call source parity"
  else
    IO.println "FAIL compile_prog parity"
  pure parityGuard

end Flapjack.Test.CompileProgParity
