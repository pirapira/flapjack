import Flapjack.Pancake.PanToCrep.Compile

namespace Flapjack.Test.CompileToCrepeParity

open Flapjack

/-! Direct `raise_const` result from `compile_to_crep_probe.out`, now checked
at the exact HOL declaration-only boundary over a 64-bit word. The exception
declaration determines code zero internally; no compiler context is supplied. -/
def holDeclarationOnlyProbe : List (Decl (BitVec 64)) :=
  [.exnDecl "E" .one,
   .function
     { name := "f", inline := false, exported := false,
       params := [("x", .one)],
       body := .raise "E" (.const 7), returnShape := .one }]

def holDeclarationOnlyOracle : Bool :=
  match compileToCrepHOL holDeclarationOnlyProbe with
  | [("f", [0],
      .seq (.dec 1 (.const seven)
        (.seq (.storeGlob address (.var 1)) .skip))
        (.raise code))] =>
      seven == (7 : BitVec 64) && address == (0 : BitVec 64) &&
        code == (0 : BitVec 64)
  | _ => false

#guard holDeclarationOnlyOracle

/-! These declaration-only fixtures replay the `raise_pair` and
`handled_pair` rows from the direct HOL `compile_to_crep_probe.out` at its
concrete 8-bit word instantiation. They exercise the exact finite-map
`compileToCrepHOL` path used by `compileFlapjackEntryCake`, rather than the
older caller-context compatibility helper below. -/
def holPairRaiseProbe : List (Decl (BitVec 8)) :=
  [.exnDecl "E" (.comb [.one, .one]),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .raise "E" (.rStruct [.const 7, .const 9]),
       returnShape := .one }]

def holPairRaiseProductionOracle : Bool :=
  match compileToCrepHOL holPairRaiseProbe with
  | [("f", [], .seq
      (.dec 1 (.const seven)
        (.dec 2 (.const nine)
          (.seq (.storeGlob first (.var 1))
            (.seq (.storeGlob second (.var 2)) .skip))))
      (.raise code))] =>
      seven == (7 : BitVec 8) && nine == (9 : BitVec 8) &&
        first == (0 : BitVec 8) && second == (1 : BitVec 8) &&
        code == (0 : BitVec 8)
  | _ => false

#guard holPairRaiseProductionOracle

def holLaterPairRaiseProbe : List (Decl (BitVec 8)) :=
  [.exnDecl "E" (.comb [.one, .one]),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .dec "a" .one (.const 3)
         (.dec "b" .one (.const 5)
           (.raise "E" (.rStruct [.const 7, .const 9]))),
       returnShape := .one }]

def holLaterPairRaiseProductionOracle : Bool :=
  match compileToCrepHOL holLaterPairRaiseProbe with
  | [("f", [],
      .dec 1 (.const three)
        (.dec 2 (.const five)
          (.seq
            (.dec 3 (.const seven)
              (.dec 4 (.const nine)
                (.seq
                  (.storeGlob first (.var 3))
                  (.seq (.storeGlob second (.var 4)) .skip))))
            (.raise code))))] =>
      three == (3 : BitVec 8) && five == (5 : BitVec 8) &&
        seven == (7 : BitVec 8) && nine == (9 : BitVec 8) &&
        first == (0 : BitVec 8) && second == (1 : BitVec 8) &&
        code == (0 : BitVec 8)
  | _ => false

#guard holLaterPairRaiseProductionOracle

def holHandledPairProbe : List (Decl (BitVec 8)) :=
  [.exnDecl "E" (.comb [.one, .one]),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .raise "E" (.rStruct [.const 7, .const 9]),
       returnShape := .comb [.one, .one] },
   .function
     { name := "g", inline := false, exported := false,
       params := [("pair", .comb [.one, .one])],
       body := .call
         (some (some (.local, "pair"), some ("E", "pair", .skip))) "f" [],
       returnShape := .one }]

def holHandledPairProductionOracle : Bool :=
  match compileToCrepHOL holHandledPairProbe with
  | [("f", [], .seq
        (.dec 1 (.const seven)
          (.dec 2 (.const nine)
            (.seq (.storeGlob first (.var 1))
              (.seq (.storeGlob second (.var 2)) .skip))))
        (.raise raiseCode)),
     ("g", [0, 1], .call
        (some ([0, 1], some (handlerCode,
          .seq
            (.seq (.assign 0 (.loadGlob loadFirst))
              (.seq (.assign 1 (.loadGlob loadSecond)) .skip))
            .skip))) "f" [])] =>
      seven == (7 : BitVec 8) && nine == (9 : BitVec 8) &&
        first == (0 : BitVec 8) && second == (1 : BitVec 8) &&
        raiseCode == (0 : BitVec 8) && handlerCode == (0 : BitVec 8) &&
        loadFirst == (0 : BitVec 8) && loadSecond == (1 : BitVec 8)
  | _ => false

#guard holHandledPairProductionOracle

def holHandledPairMetadataAdapterOracle : Bool :=
  match compileToCrepHOLWithMetadata holHandledPairProbe with
  | [{ name := "f", params := [], returnShape := .comb [.one, .one], .. },
     { name := "g", params := [0, 1], returnShape := .one, .. }] => true
  | _ => false

#guard holHandledPairMetadataAdapterOracle

def holMetadataAdapterOracle : Bool :=
  match compileToCrepHOLWithMetadata holDeclarationOnlyProbe with
  | [{ name := "f", params := [0], returnShape := .one, .. }] => true
  | _ => false

#guard holMetadataAdapterOracle

/-! HOL `alist_to_fmap` is a right fold: the first repeated name wins even
though `compile_to_crep` still emits both function declarations in order. -/
def holDuplicateMapOracle : Bool :=
  let declarations : List (Decl (BitVec 64)) :=
    [.exnDecl "E" .one, .exnDecl "E" .one,
     .function
       { name := "f", inline := false, exported := false,
         params := [], body := .skip, returnShape := .one },
     .function
       { name := "f", inline := false, exported := false,
         params := [("x", .one)], body := .skip,
         returnShape := .comb [.one, .one] }]
  FLOOKUP (panToCrepGetEidsFromDeclsHOL declarations) "E" ==
      some (0 : BitVec 64) &&
    (match FLOOKUP (functionInfosHOL declarations) "f" with
     | some ([], .one) => true
     | _ => false) &&
    (compileToCrepHOL declarations).length == 2

#guard holDuplicateMapOracle

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

def laterPairDecls : List (Decl Nat) :=
  [.exnDecl "E" (.comb [.one, .one]),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .dec "a" .one (.const 3)
         (.dec "b" .one (.const 5)
           (.raise "E" (.rStruct [.const 7, .const 9]))),
       returnShape := .one }]

/-! Direct `raise_pair_later` result from `compile_to_crep_probe.out`.  Two
    ordinary declarations first consume the word-strided slots 1 and 2, so a
    two-word exception payload lowered afterwards must take the later,
    contiguous Temp slots 3 and 4 and store them at the one-word Crep global
    indices `0w`/`1w` (not byte-scaled), even at target byte width 8. -/
def laterPairOracle : Bool :=
  match compileToCrep compileToCrepePairContext laterPairDecls with
  | [{ name := "f", params := [],
       body := .dec 1 (.const 3)
         (.dec 2 (.const 5)
           (.seq
             (.dec 3 (.const 7)
               (.dec 4 (.const 9)
                 (.seq (.storeGlob 0 (.var 3))
                   (.seq (.storeGlob 1 (.var 4)) .skip))))
             (.raise 0))),
       returnShape := .one }] => true
  | _ => false

#guard laterPairOracle

def handledPairDecls : List (Decl Nat) :=
  [.exnDecl "E" (.comb [.one, .one]),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .raise "E" (.rStruct [.const 7, .const 9]),
       returnShape := .comb [.one, .one] },
   .function
     { name := "g", inline := false, exported := false,
       params := [("pair", .comb [.one, .one])],
       body := .call
         (some (some (.local, "pair"), some ("E", "pair", .skip))) "f" [],
       returnShape := .one }]

/-! Direct `handled_pair` row in `compile_to_crep_probe.out`: the function
    raises a two-field RStruct payload, and the handled call carries both its
    two-word result slots and the exception handler that reloads both payload
    words from the Crep global return area. -/
def handledPairOracle : Bool :=
  match compileToCrep compileToCrepePairContext handledPairDecls with
  | [{ name := "f", params := [],
       body := .seq
         (.dec 1 (.const 7)
           (.dec 2 (.const 9)
             (.seq (.storeGlob 0 (.var 1))
               (.seq (.storeGlob 1 (.var 2)) .skip))))
         (.raise 0), returnShape := .comb [.one, .one] },
     { name := "g", params := [0, 1],
       body := .call
         (some ([0, 1], some (0,
           .seq (.seq (.assign 0 (.loadGlob 0))
             (.seq (.assign 1 (.loadGlob 1)) .skip)) .skip)))
         "f" [], returnShape := .one }] => true
  | _ => false

#guard handledPairOracle

def callOracleContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 0)],
    maxVar := 0, bytesInWord := 8 }

def globalDestinationDecls : List (Decl Nat) :=
  [.function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .comb [.one, .one] },
   .function
     { name := "g", inline := false, exported := false,
       params := [("pair", .comb [.one, .one])],
       body := .call (some (some (.global, "pair"), none)) "f" [],
       returnShape := .one }]

/-! Direct `global_dest` row in `compile_prog_probe.out`.  The source kind
    is ignored at this boundary; the global-tagged destination still receives
    the two flattened parameter slots. -/
def globalDestinationOracle : Bool :=
  match compileToCrep callOracleContext globalDestinationDecls with
  | [{ name := "f", params := [], body := .skip, returnShape := .comb [.one, .one] },
     { name := "g", params := [0, 1],
       body := .call (some ([0, 1], none)) "f" [],
       returnShape := .one }] => true
  | _ => false

#guard globalDestinationOracle

def handledMissingDestinationDecls : List (Decl Nat) :=
  [.exnDecl "E" (.comb [.one, .one]),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .skip, returnShape := .comb [.one, .one] },
   .function
     { name := "g", inline := false, exported := false,
       params := [("pair", .comb [.one, .one])],
       body := .call
         (some (some (.local, "missing"), some ("E", "pair", .skip))) "f" [],
       returnShape := .one }]

/-! Direct `handled_missing_dest` row in `compile_prog_probe.out`. -/
def handledMissingDestinationOracle : Bool :=
  match compileToCrep callOracleContext handledMissingDestinationDecls with
  | [{ name := "f", params := [], body := .skip, returnShape := .comb [.one, .one] },
     { name := "g", params := [0, 1],
       body := .call (some ([], some (0,
         .seq (.seq (.assign 0 (.loadGlob 0))
           (.seq (.assign 1 (.loadGlob 1)) .skip)) .skip))) "f" [],
       returnShape := .one }] => true
  | _ => false

#guard handledMissingDestinationOracle

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
  let results := [
    ("raised constant", parityGuard),
    ("declaration-only two-word exception", holPairRaiseProductionOracle),
    ("declaration-only later two-word exception", holLaterPairRaiseProductionOracle),
    ("declaration-only handled two-word exception", holHandledPairProductionOracle),
    ("handled-call production metadata adapter", holHandledPairMetadataAdapterOracle),
    ("two-word exception", pairRaiseOracle),
    ("later two-word exception", laterPairOracle),
    ("handled two-word exception", handledPairOracle),
    ("global call destination", globalDestinationOracle),
    ("handled call with missing destination", handledMissingDestinationOracle),
    ("flattened parameters", crepVarsOracle)]
  for (name, passed) in results do
    IO.println s!"{if passed then "PASS" else "FAIL"} compile_to_crep {name}"
  pure (results.all Prod.snd)

end Flapjack.Test.CompileToCrepeParity
