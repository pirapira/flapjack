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
  | [("pair", (.comb [.one, .one], [1, 2])), ("x", (.one, [0]))] => true
  | _ => false

#guard makeVmapOracle

/-! Cake's `FEMPTY |++ ZIP` gives the later duplicate parameter the result of
    lookup.  This is deliberately a malformed direct compiler input: the
    source static checker rejects duplicate formal names, but the executable
    `make_vmap` boundary must still agree with the HOL definition. -/
def duplicateVmapOracle : Bool :=
  match lookupInfo "x" (panToCrepMakeVmap
      [("x", .one), ("x", .comb [.one, .one])]) with
  | some (.comb [.one, .one], [1, 2]) => true
  | _ => false

#guard duplicateVmapOracle

def duplicateFunctionDecls : List (Decl Nat) :=
  [.function
      { name := "dup", inline := false, exported := false, params := [],
        body := .return (.const 1), returnShape := .one },
   .function
      { name := "dup", inline := false, exported := false,
        params := [("x", .one)], body := .return (.var .local "x"),
        returnShape := .one }]

/-! `make_funcs_def` is the same first-binding finite-map construction as
    `ALOOKUP`; the first duplicate therefore remains visible. -/
def duplicateFuncsOracle : Bool :=
  match lookupInfo "dup" (functionInfos duplicateFunctionDecls) with
  | some ([], .one) => true
  | _ => false

#guard duplicateFuncsOracle

/-! Cake's `FEMPTY |++ ZIP` gives the later duplicate parameter binding to
    `FLOOKUP`; the list-backed source map therefore keeps the later slot first.
    The body probe makes the selected slot observable at the Crepe boundary. -/
def duplicateParameterLastWinsOracle : Bool :=
  match panToCrepMakeVmap [("x", .one), ("x", .one)] with
  | [("x", (.one, [1])), ("x", (.one, [0]))] =>
      match panToCrepCompFunc compileToCrepeProbeContext
          [("x", .one), ("x", .one)]
          (.return (.var .local "x")) with
      | .return [.var 1] => true
      | _ => false
  | _ => false

#guard duplicateParameterLastWinsOracle

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

def compileToCrepePairContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 0)],
    maxVar := 0, bytesInWord := 8 }

def compileToCrepePairDecls : List (Decl Nat) :=
  [.exnDecl "E" (.comb [.one, .one]),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .raise "E" (.rStruct [.const 7, .const 9]),
       returnShape := .one }]

/-! Direct `raise_pair` result from `compile_to_crep_probe.out`.  In
    particular, the Crep global return area is word-indexed (0, 1), even when
    the target byte width is 8. -/
def pairRaiseOracle : Bool :=
  match compileToCrep compileToCrepePairContext compileToCrepePairDecls with
  | [{ name := "f", params := [],
       body := .seq
         (.dec 1 (.const 7)
           (.dec 2 (.const 9)
             (.seq (.storeGlob 0 (.var 1))
               (.seq (.storeGlob 1 (.var 2)) .skip))))
         (.raise 0),
       returnShape := .one }] => true
  | _ => false

#guard pairRaiseOracle

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
  pure (parityGuard && pairRaiseOracle && crepVarsOracle)

end Flapjack.Test.CompileToCrepeParity
