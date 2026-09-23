import Flapjack.Pancake.PanToCrep.Compile

/-!
# Original-domain parity for `pan_to_crep$compile` (`compile_def`)

The expected cases come from the direct HOL-EVAL fixture
`scripts/hol-probes/compile_def_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:139-305`.
-/

namespace Flapjack.Test.CompileDefParity

open Flapjack

def context : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 1 }

def fixedWidthContext : PanToCrepCompileContext Nat :=
  { vars := [("p", (.one, [0])), ("x", (.one, [1])), ("y", (.one, [2]))]
    functions := []
    exceptions := []
    maxVar := 2 }

def pairLoad : Prog Nat :=
  .return (.load (.comb [.one, .one]) (.var .local "p"))

def pairStore : Prog Nat :=
  .store (.var .local "p") (.rStruct [.var .local "x", .var .local "y"])

def emptyStructReturn : Prog Nat := .return (.rStruct [])

def isFixedPairLoad8 : CrepProg Nat → Bool
  | .return [.load (.var 0), .load (.op .add [.var 0, .const 8])] => true
  | _ => false

def isFixedPairStore8 : CrepProg Nat → Bool
  | .dec 3 (.var 0) (.dec 4 (.var 1) (.dec 5 (.var 2)
      (.seq (.store (.var 3) (.var 4))
        (.seq (.store (.op .add [.var 3, .const 8]) (.var 5)) .skip)))) => true
  | _ => false

def fixedWidthParityGuard : Bool :=
  isFixedPairLoad8 (compileProgFixed fixedWidthContext pairLoad) &&
  isFixedPairStore8 (compileProgFixed fixedWidthContext pairStore)

def emptyOneGlobalContext : CompileContext Nat :=
  { vars := [("empty_one", (.one, []))], functions := [], exceptions := [],
    maxVar := 0, bytesInWord := 1 }

def extraNamesGlobalContext : CompileContext Nat :=
  { vars := [("extra_names", (.one, [4, 5]))], functions := [], exceptions := [],
    maxVar := 5, bytesInWord := 1 }

def missingNamesGlobalContext : CompileContext Nat :=
  { vars := [("missing_names", (.comb [.one, .one], [4]))],
    functions := [], exceptions := [], maxVar := 4, bytesInWord := 1 }

def missingGlobalCall : Prog Nat :=
  .call (some (some (.global, "missing"), none)) "f" []

def emptyOneGlobalCall : Prog Nat :=
  .call (some (some (.global, "empty_one"), none)) "f" []

def extraNamesGlobalCall : Prog Nat :=
  .call (some (some (.global, "extra_names"), none)) "f" []

def missingNamesGlobalCall : Prog Nat :=
  .call (some (some (.global, "missing_names"), none)) "f" []

def isTailCallToF : CrepProg Nat → Bool
  | .call none "f" [] => true
  | _ => false

def isExtraNamesCallToF : CrepProg Nat → Bool
  | .call (some ([4, 5], none)) "f" [] => true
  | _ => false

def isMissingNamesCallToF : CrepProg Nat → Bool
  | .call (some ([4], none)) "f" [] => true
  | _ => false

def isSkip : CrepProg Nat → Bool
  | .skip => true
  | _ => false

def isReturnSeven : CrepProg Nat → Bool
  | .return [.const 7] => true
  | _ => false

def isEmptyReturn : CrepProg Nat → Bool
  | .return [] => true
  | _ => false

def isBreak : CrepProg Nat → Bool
  | .break 0 => true
  | _ => false

def isContinue : CrepProg Nat → Bool
  | .continue 0 => true
  | _ => false

def isSeqSkipTick : CrepProg Nat → Bool
  | .seq .skip .tick => true
  | _ => false

def parityGuard : Bool :=
  isSkip (compileProg context (.skip : Prog Nat)) &&
  isReturnSeven (compileProg context (.return (.const 7))) &&
  isEmptyReturn (compileProg context emptyStructReturn) &&
  isBreak (compileProg context (.break : Prog Nat)) &&
  isContinue (compileProg context (.continue : Prog Nat)) &&
  isSeqSkipTick (compileProg context (.seq .skip (.tick : Prog Nat))) &&
  isTailCallToF (compileProg context missingGlobalCall) &&
  isTailCallToF (compileProg emptyOneGlobalContext emptyOneGlobalCall) &&
  isExtraNamesCallToF (compileProg extraNamesGlobalContext extraNamesGlobalCall) &&
  isMissingNamesCallToF (compileProg missingNamesGlobalContext missingNamesGlobalCall) &&
  fixedWidthParityGuard

example : compileProg context missingGlobalCall = .call none "f" [] := by
  simp [missingGlobalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, context, lookupInfo]

example : compileProg context emptyStructReturn = .return [] := by
  simp [emptyStructReturn, compileProg, compileExp, compileExp.compileExpList,
    Shape.shapeSize]

example :
    compileProg emptyOneGlobalContext emptyOneGlobalCall = .call none "f" [] := by
  simp [emptyOneGlobalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, emptyOneGlobalContext, lookupInfo]

example :
    compileProg extraNamesGlobalContext extraNamesGlobalCall =
      .call (some ([4, 5], none)) "f" [] := by
  simp [extraNamesGlobalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, extraNamesGlobalContext, lookupInfo]

example :
    compileProg missingNamesGlobalContext missingNamesGlobalCall =
      .call (some ([4], none)) "f" [] := by
  simp [missingNamesGlobalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, missingNamesGlobalContext, lookupInfo]

#eval parityGuard
#guard parityGuard
#guard fixedWidthParityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS compile_def fixed-width load/store and control-flow parity"
  else
    IO.println "FAIL compile_def parity"
  pure parityGuard

end Flapjack.Test.CompileDefParity
