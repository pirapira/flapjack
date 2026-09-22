import Flapjack.Pancake.CrepToLoop

/-!
`crep_to_loop$compile (Dec v e prog)` (`crep_to_loopScript.sml:409-415`)
compiles the body under `fl = insert tmp () l`: the *incoming* live set plus
the declared variable's new temporary.  The set `compile_exp` returned is
deliberately dropped, so the temporaries `compile_exp` inserts for
`LoadByte`, `Load32`, `Cmp` and `Crepop` do not reach any cutset the body
emits.  They are still inserted where they are genuinely live -- the `If`
that `prog_if` builds for a `Cmp` keeps them -- which is what distinguishes
this from simply never inserting them.

The oracle below is the `crep_to_loop$comp_func` output for the `main'` of
`Flapjack/Test/OriginalPancake/dec_temporary_cutset.pnk`'s `byte_dec` shape,
evaluated by the original CakeML definitions through
`scripts/hol-probes/pancake-stage-probeScript.sml`.
-/
namespace Flapjack.Test.CrepToLoopDecLive

open Flapjack

/-- `pan_to_crep$compile_prog`'s body for the minimised register-pressure
    function: `Dec x; Dec y = ld8 1008; Dec p0; Dec p1; p := pair(1,2);
    while (0 < x) { if (1 <= p1) {} }; add1(p1, y)`.  Cake prints exactly this
    as `stage=pan_to_crep`. -/
def crepBody : CrepProg Nat :=
  .dec 1 (.const 7)
    (.dec 2 (.loadByte (.const 1008))
      (.dec 3 (.const 0)
        (.dec 4 (.const 0)
          (.seq (.call (some ([3, 4], none)) "pair" [.const 1, .const 2])
            (.seq
              (.while (.cmp .less (.const 0) (.var 1))
                (.ite (.cmp .notLess (.const 1) (.var 4)) .skip .skip))
              (.call none "add1" [.var 4, .var 2]))))))

def context : LoopContext Nat :=
  { vars := [], functions := [("pair", (66, 2)), ("add1", (65, 2))],
    maxVar := 0, target := .rv64i }

def compiled : LoopProg Nat := compileCrepToLoop context [] crepBody

/-- Every cutset the compiled program carries, in traversal order. -/
def cutsets : LoopProg Nat → List (List Nat)
  | .seq first second => cutsets first ++ cutsets second
  | .mark body => cutsets body
  | .ite _ _ _ thenBranch elseBranch live =>
      cutsets thenBranch ++ cutsets elseBranch ++ [live]
  | .loop liveIn body liveOut => [liveIn] ++ cutsets body ++ [liveOut]
  | .call returns _ _ handler =>
      (match returns with | some (_, live) => [live] | none => []) ++
      (match handler with
       | some (_, handlerCode, normal, live) =>
           cutsets handlerCode ++ cutsets normal ++ [live]
       | none => [])
  | .ffi _ _ _ _ _ live => [live]
  | _ => []

/-- `stage=crep_to_loop_comp`: the call cutset and its handler live-out are
    `⦕1; 3; 4; 5⦖`; loop var `2` is the `LoadByte` temporary and Cake keeps it
    out of both. -/
def callCutsetMatches : Bool :=
  (cutsets compiled).take 3 == [[1, 3, 4, 5], [1, 3, 4, 5], [1, 3, 4, 5]]

/-- `Loop ⦕1; 3; 4; 5⦖ ... ⦕1; 3; 4; 5⦖` likewise excludes the temporary. -/
def loopCutsetMatches : Bool :=
  let sets := cutsets compiled
  sets.contains [1, 3, 4, 5] && !sets.any (fun live => live.contains 2)

/-- The comparison `If` that `prog_if` builds keeps `compile_exp`'s own
    temporaries `7` and `8`: Cake prints `⦕1; 3; 4; 5; 7; 8⦖` there, so the
    `Dec` fix must not be a blanket suppression of inserted temporaries. -/
def comparisonCutsetKeepsItsTemporaries : Bool :=
  (cutsets compiled).contains [1, 3, 4, 5, 7, 8]

#guard callCutsetMatches
#guard loopCutsetMatches
#guard comparisonCutsetKeepsItsTemporaries

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("crep_to_loop Dec keeps the initializer temporary out of a call cutset",
        callCutsetMatches)
    , ("crep_to_loop Dec keeps the initializer temporary out of a loop cutset",
        loopCutsetMatches)
    , ("crep_to_loop still records a comparison's own temporaries",
        comparisonCutsetKeepsItsTemporaries) ]
  let mut ok := true
  for (label, passed) in checks do
    if passed then IO.println s!"PASS {label}" else IO.println s!"FAIL {label}"
    ok := ok && passed
  pure ok

end Flapjack.Test.CrepToLoopDecLive
