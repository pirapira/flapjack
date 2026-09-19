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

/-! Direct `make_funcs_def` oracle: exception declarations are skipped and the
    function entry preserves both source parameters and return shape. -/
def makeFuncsOracle : Bool :=
  match panToCrepMakeFuncs compileToCrepeProbeDecls with
  | [("f", ([("x", .one)], .one))] => true
  | _ => false

#guard makeFuncsOracle

/-! Direct `crep_vars_def` oracle: nested parameter shapes flatten in source
    order and receive consecutive slots. -/
def crepVarsOracle : Bool :=
  panToCrepVars [("left", .one), ("pair", .comb [.one, .one]),
      ("right", .one)] == [0, 1, 2, 3]

#guard crepVarsOracle
/-! Direct `make_vmap_def` oracle: shaped parameters receive consecutive
    flattened slots in source order. -/
def makeVmapOracle : Bool :=
  match panToCrepMakeVmap [("x", .one), ("pair", .comb [.one, .one])] with
  | [("x", (.one, [0])), ("pair", (.comb [.one, .one], [1, 2]))] => true
  | _ => false

#guard makeVmapOracle

/-! Direct `comp_func_def` oracle: the source-shaped wrapper uses the
    flattened parameter shape to choose `vmax` and preserves the compiled
    raise body from the Cake fixture. -/
def compFuncOracle : Bool :=
  match panToCrepCompFunc compileToCrepeProbeContext [("x", .one)]
      (.raise "E" (.const 7)) with
  | .seq (.dec 1 (.const 7) (.seq (.storeGlob 0 (.var 1)) .skip))
      (.raise 0) => true
  | _ => false

#guard compFuncOracle

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
    panToCrepCompFunc, panToCrepVars, Shape.shapeSize,
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
  pure (parityGuard && crepVarsOracle)

end Flapjack.Test.CompileToCrepeParity
