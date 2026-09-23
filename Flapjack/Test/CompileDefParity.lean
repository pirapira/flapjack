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

def finiteMapContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE (FUPDATE FEMPTY ("p", (.one, [3]))) ("p", (.one, [5]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 5 }

def fixedWidthHOLContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE_LIST FEMPTY
      [("p", (.one, [0])), ("x", (.one, [1])), ("y", (.one, [2]))]
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 2 }

def emptyHOLContext : PanToCrepHOLContext Nat :=
  { vars := FEMPTY, funcs := FEMPTY, eids := FEMPTY, vmax := 0 }

def emptyOneHOLContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE FEMPTY ("empty_one", (.one, []))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 0 }

def highTailHOLContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE_LIST FEMPTY
      [("ptr1", (.one, [4, 100])), ("len1", (.one, [5])),
       ("ptr2", (.one, [6])), ("len2", (.one, [7]))]
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 100 }

def highTailExtCall : Prog Nat :=
  .extCall "f" (.var .local "ptr1") (.var .local "len1")
    (.var .local "ptr2") (.var .local "len2")

def extraNamesHOLContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE FEMPTY ("extra_names", (.one, [4, 5]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 5 }

def missingNamesHOLContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE FEMPTY ("missing_names", (.comb [.one, .one], [4]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 4 }

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

def finiteMapParityGuard : Bool :=
  match compileProgHOL finiteMapContext (.return (.var .local "p")) with
  | .return [.var 5] => true
  | _ => false

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

def validLocalContext : CompileContext Nat :=
  { vars := [("pair", (.comb [.one, .one], [0, 1]))], functions := [],
    exceptions := [], maxVar := 1, bytesInWord := 1 }

def emptyOneLocalContext : CompileContext Nat :=
  { vars := [("empty_one", (.one, []))], functions := [], exceptions := [],
    maxVar := 0, bytesInWord := 1 }

def extraNamesLocalContext : CompileContext Nat :=
  { vars := [("extra_names", (.one, [4, 5]))], functions := [], exceptions := [],
    maxVar := 5, bytesInWord := 1 }

def missingNamesLocalContext : CompileContext Nat :=
  { vars := [("missing_names", (.comb [.one, .one], [4]))],
    functions := [], exceptions := [], maxVar := 4, bytesInWord := 1 }

def missingLocalCall : Prog Nat :=
  .call (some (some (.local, "missing"), none)) "f" []

def emptyOneLocalCall : Prog Nat :=
  .call (some (some (.local, "empty_one"), none)) "f" []

def extraNamesLocalCall : Prog Nat :=
  .call (some (some (.local, "extra_names"), none)) "f" []

def missingNamesLocalCall : Prog Nat :=
  .call (some (some (.local, "missing_names"), none)) "f" []

def validLocalCall : Prog Nat :=
  .call (some (some (.local, "pair"), none)) "f" []

def isTailCallToF : CrepProg Nat → Bool
  | .call none "f" [] => true
  | _ => false

def isValidPairCallToF : CrepProg Nat → Bool
  | .call (some ([0, 1], none)) "f" [] => true
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

def isHighTailExtCall : CrepProg Nat → Bool
  | .dec 101 (.var 4) (.dec 102 (.var 5) (.dec 103 (.var 6)
      (.dec 104 (.var 7) (.extCall "f" 101 102 103 104)))) => true
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

def nativeProgramParityGuard : Bool :=
  isSkip (compileProgHOL emptyHOLContext (.skip : Prog Nat)) &&
  isReturnSeven (compileProgHOL emptyHOLContext (.return (.const 7))) &&
  isEmptyReturn (compileProgHOL emptyHOLContext emptyStructReturn) &&
  isBreak (compileProgHOL emptyHOLContext (.break : Prog Nat)) &&
  isContinue (compileProgHOL emptyHOLContext (.continue : Prog Nat)) &&
  isSeqSkipTick (compileProgHOL emptyHOLContext (.seq .skip (.tick : Prog Nat))) &&
  isHighTailExtCall (compileProgHOL highTailHOLContext highTailExtCall) &&
  isTailCallToF (compileProgHOL emptyHOLContext missingGlobalCall) &&
  isTailCallToF (compileProgHOL emptyOneHOLContext emptyOneGlobalCall) &&
  isExtraNamesCallToF (compileProgHOL extraNamesHOLContext extraNamesGlobalCall) &&
  isMissingNamesCallToF (compileProgHOL missingNamesHOLContext missingNamesGlobalCall)

def finiteMapLoadStoreParityGuard : Bool :=
  isFixedPairLoad8 (compileProgHOL fixedWidthHOLContext pairLoad) &&
  isFixedPairStore8 (compileProgHOL fixedWidthHOLContext pairStore)

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
  isTailCallToF (compileProg context missingLocalCall) &&
  isTailCallToF (compileProg emptyOneLocalContext emptyOneLocalCall) &&
  isExtraNamesCallToF (compileProg extraNamesLocalContext extraNamesLocalCall) &&
  isMissingNamesCallToF (compileProg missingNamesLocalContext missingNamesLocalCall) &&
  isValidPairCallToF (compileProg validLocalContext validLocalCall) &&
  fixedWidthParityGuard && finiteMapParityGuard && nativeProgramParityGuard &&
    finiteMapLoadStoreParityGuard

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

/-! Local-kind mirrors.  Cake's rule looks the destination up in
`ctxt.vars` and discards the `rk` tag, so a Local call and its Global twin
emit the same list; the HOL fixture `compile_def_probe.out` records both. -/

example : compileProg context missingLocalCall = .call none "f" [] := by
  simp [missingLocalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, context, lookupInfo]

example :
    compileProg emptyOneLocalContext emptyOneLocalCall = .call none "f" [] := by
  simp [emptyOneLocalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, emptyOneLocalContext, lookupInfo]

example :
    compileProg extraNamesLocalContext extraNamesLocalCall =
      .call (some ([4, 5], none)) "f" [] := by
  simp [extraNamesLocalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, extraNamesLocalContext, lookupInfo]

example :
    compileProg missingNamesLocalContext missingNamesLocalCall =
      .call (some ([4], none)) "f" [] := by
  simp [missingNamesLocalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, missingNamesLocalContext, lookupInfo]

example :
    compileProg validLocalContext validLocalCall =
      .call (some ([0, 1], none)) "f" [] := by
  simp [validLocalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, validLocalContext, lookupInfo]

#eval parityGuard
#guard parityGuard
#guard fixedWidthParityGuard
#guard finiteMapParityGuard
#guard nativeProgramParityGuard
#guard finiteMapLoadStoreParityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS compile_def fixed-width load/store and control-flow parity"
  else
    IO.println "FAIL compile_def parity"
  pure parityGuard

end Flapjack.Test.CompileDefParity
