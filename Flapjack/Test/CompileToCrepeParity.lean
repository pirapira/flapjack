import Flapjack.Compile

namespace Flapjack.Test.CompileToCrepeParity

open Flapjack

def compileToCrepeProbeContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 0)],
    maxVar := 0, bytesInWord := 1 }

def compileToCrepeProbeDecls : List (Decl Nat) :=
  [.exnDecl "E" .one,
   .function
     { name := "f", inline := false, exported := false,
       params := [("x", .one)],
       body := .raise "E" (.const 7), returnShape := .one }]

/-! The fixture is the direct HOL evaluation of
    `pan_to_crep$compile_to_crep` on the same exception/function declaration.
    `compileToCrep` preserves the source function name, flattened parameter
    slot, nested payload spill, and looked-up exception code. -/
theorem compile_to_crep_raise_const_parity :
    compileToCrep compileToCrepeProbeContext compileToCrepeProbeDecls =
      [{ name := "f", params := [0],
         body := .seq
           (.dec 1 (.const 7)
             (.seq (.storeGlob 0 (.var 1)) .skip))
           (.raise 0),
         returnShape := .one }] := by
  simp [compileToCrep, compileFunctionsSource, compileFunDeclSource,
    compileParamVars,
    functionInfos, compileToCrepeProbeContext, compileToCrepeProbeDecls,
    compileProg, compileExp, freshNames, nestedDecs, storeGlobals,
    crepNestedSeq, lookupInfo]

def parityGuard : Bool :=
  match compileToCrep compileToCrepeProbeContext compileToCrepeProbeDecls with
  | [{ name := "f", params := [0],
       body := .seq
         (.dec 1 (.const 7) (.seq (.storeGlob 0 (.var 1)) .skip))
         (.raise 0), returnShape := .one }] => true
  | _ => false

#eval parityGuard
#guard
  parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS compile_to_crep raised constant source parity"
  else
    IO.println "FAIL compile_to_crep parity"
  pure parityGuard

end Flapjack.Test.CompileToCrepeParity
