import Flapjack.CrepToLoop

/-!
Direct parity for `crep_to_loop$compile` (`crep_to_loopScript.sml:120`).
The checked-in HOL fixture covers `Skip` and `Raise`; the latter observes the
compiler-generated temporary assignment before the terminal raise.
-/
namespace Flapjack.Test.CrepToLoopParity

def compileContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [], maxVar := 0, target := .rv64i }

def originalCompileSkip : LoopProg Nat := .skip

def originalCompileRaise : LoopProg Nat :=
  .seq (.assign 1 (.const 17)) (.raise 1)

def leanCompileSkip : LoopProg Nat :=
  compileCrepToLoop compileContext [] (.skip : CrepProg Nat)

def leanCompileRaise : LoopProg Nat :=
  compileCrepToLoop compileContext [] (.raise 17 : CrepProg Nat)

#eval leanCompileSkip
#eval leanCompileRaise

def parityGuard : Bool :=
  match leanCompileSkip, originalCompileSkip, leanCompileRaise, originalCompileRaise with
  | .skip, .skip,
    .seq (.assign 1 (.const 17)) (.raise 1),
    .seq (.assign 1 (.const 17)) (.raise 1) => true
  | _, _, _, _ => false

#eval parityGuard
#guard parityGuard

/-- Context used for the call-lowering characterization. Function `1` maps to
    loop label `3`, so the generated call targets `some 3`. -/
def callContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [("f", (3, 1))], maxVar := 4, target := .rv64i }

/-- `crep_to_loop$compile` on `call (SOME ([9], NONE)) 1 [Const 3]`.

    The original always emits a default handler `rt2` for a call returning
    through an exception channel (`crep_to_loopScript.sml:193-206`); for
    `handler = NONE` that `rt2` binds the caught exception and immediately
    re-raises it, which is observationally indistinguishable from an absent
    source handler. -/
def leanCompileCallNoHandler : LoopProg Nat :=
  compileCrepToLoop callContext [] (.call (some ([9], none)) "f" [.const 3])

/-- `crep_to_loop$compile` on a call that names an exception handler, which
    must carry an `rt2` handler exactly like the original. -/
def leanCompileCallWithHandler : LoopProg Nat :=
  compileCrepToLoop callContext []
    (.call (some ([9], some (7, .skip))) "f" [.const 3])

/-- A handler-less source call still carries Cake's default raise handler. -/
def handlerlessCallCarriesRaiseHandler : Bool :=
  match leanCompileCallNoHandler with
  | .seq _ (.call _ (some 3) _ (some (5, .raise 5, .skip, []))) => true
  | _ => false

/-- A call that names an exception handler does emit an `rt2`. -/
def handledCallCarriesRaiseHandler : Bool :=
  match leanCompileCallWithHandler with
  | .seq _ (.call _ (some 3) _ (some _)) => true
  | _ => false

#eval leanCompileCallNoHandler
#eval leanCompileCallWithHandler

#guard handlerlessCallCarriesRaiseHandler
#guard handledCallCarriesRaiseHandler

/-! Cake's `crep_to_loop$compile` resolves all four ExtCall operands through
`ctxt.vars` (`crep_to_loopScript.sml:198-213`).  Keep both sides of that
oracle explicit: a complete context emits the mapped FFI payload, while a
missing lookup emits `Skip` rather than leaking an unresolved source slot. -/
def ffiContext : LoopContext Nat :=
  { vars := [(10, 41), (11, 42), (12, 43), (13, 44)],
    functions := [], maxVar := 20, target := .rv64i }

def ffiContextMapped : LoopProg Nat :=
  compileCrepToLoop ffiContext [7]
    (.extCall "halt" 10 11 12 13)

def ffiContextMappingMatches : Bool :=
  match ffiContextMapped with
  | .ffi function configuration configurationLength array arrayLength live =>
      function == "halt" && configuration == 41 &&
        configurationLength == 42 && array == 43 && arrayLength == 44 &&
        live == [7]
  | _ => false

def ffiContextMissing : LoopContext Nat :=
  { ffiContext with vars := [(10, 41), (11, 42), (12, 43)] }

def ffiMissingLookupSkips : Bool :=
  match compileCrepToLoop ffiContextMissing [7]
      (.extCall "halt" 10 11 12 13) with
  | .skip => true
  | _ => false

#guard ffiContextMappingMatches
#guard ffiMissingLookupSkips

/-! Cake resolves a shared-memory destination through `find_var` too
(`crep_to_loopScript.sml:214`); retaining the raw source slot changes the
post-loop store in the hello oracle. -/
def shMemContext : LoopContext Nat :=
  { vars := [(3, 8)], functions := [], maxVar := 0, target := .rv64i }

def leanCompileShMemMapped : LoopProg Nat :=
  compileCrepToLoop shMemContext [] (.shMem .store 3 (.var 1))

def shMemDestinationMappingMatches : Bool :=
  match leanCompileShMemMapped with
  | .seq .skip (.shMem .store 8 (.var 1)) => true
  | _ => false

#guard shMemDestinationMappingMatches

def assignDestinationMappingMatches : Bool :=
  match compileCrepToLoop shMemContext [] (.assign 3 (.var 1)) with
  | .seq .skip (.assign 8 (.var 1)) => true
  | _ => false

#guard assignDestinationMappingMatches

/-- Context for the comparison-lowering characterization. Variable `5` is a
    local that is live across the comparison (for example a value assigned
    before a `while`). -/
def comparisonContext : LoopContext Nat :=
  { vars := [(1, 5)], functions := [], maxVar := 0, target := .rv64i }

/-- `crep_to_loop$compile` on `Assign 1 (Cmp Less (Var 3) (Var 5))` with an
    incoming live set containing `5`. The comparison case threads the incoming
    live set into the materialising `ite`'s live field
    (`loopListInsert [leftTemp, rightTemp] live`, `crep_to_loopScript.sml`), so a
    value that is live across the comparison is retained by `loop_live`.
    Dropping that set made `loopShrink` delete the pre-loop assignment and the
    result variable read back the stale value (bead flapjack-8tb.1; original
    CakeML keeps `ori a0,zero,7` and returns 7 for the minimal reproducer). -/
def leanCompileComparisonKeepingLive : LoopProg Nat :=
  compileCrepToLoop comparisonContext [5] (.assign 1 (.cmp .less (.var 3) (.var 5)))

/-- All live sets attached to `ite` nodes in a loop program. -/
def loopIteLives : LoopProg Nat → List (List Nat)
  | .ite _ _ _ _ _ live => [live]
  | .seq first second => loopIteLives first ++ loopIteLives second
  | .loop _ body _ => loopIteLives body
  | .call _ _ _ (some (_, handler, _, _)) => loopIteLives handler
  | _ => []

/-- The materialising comparison keeps the incoming live variable. -/
def comparisonKeepsIncomingLive : Bool :=
  (loopIteLives leanCompileComparisonKeepingLive).any (fun live => live.contains 5)

/-- With no incoming live variable the comparison does not invent one. -/
def comparisonWithoutLiveDropsIt : Bool :=
  !((loopIteLives (compileCrepToLoop comparisonContext []
        (.assign 1 (.cmp .less (.var 3) (.const 2))))).any (fun live => live.contains 5))

#eval leanCompileComparisonKeepingLive
#guard comparisonKeepsIncomingLive
#guard comparisonWithoutLiveDropsIt

def runChecks : IO Bool := do
  let results := [handlerlessCallCarriesRaiseHandler, handledCallCarriesRaiseHandler,
    shMemDestinationMappingMatches, assignDestinationMappingMatches,
    comparisonKeepsIncomingLive,
    comparisonWithoutLiveDropsIt]
  let names := [
    "crep_to_loop default call handler",
    "crep_to_loop explicit call handler",
    "crep_to_loop shared-memory destination mapping",
    "crep_to_loop assignment destination mapping",
    "crep_to_loop comparison keeps the incoming live set",
    "crep_to_loop comparison without live does not invent one"]
  let mut all := true
  for (name, result) in names.zip results do
    if result then IO.println s!"PASS {name}" else IO.println s!"FAIL {name}"
    all := all && result
  pure all

end Flapjack.Test.CrepToLoopParity
