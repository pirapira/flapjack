import Flapjack.RiscV.PipelineDiagnostics

/-!
# Word-to-Stack frame containment

`word_to_stack$compile_prog` (`word_to_stackScript.sml:586-593`) sizes a
function's frame from `max_var prog DIV 2 + 1 - reg_count` of the program it
is lowering -- the output of `word_alloc`.  Flapjack used to recover that
number by running a second, complete allocation of a differently prepared
program (`cakeWordStackVarCount` on the unflattened body), which has no
counterpart upstream and can come out either above or below the real one.

When it comes out below, the register allocator's own stack slots fall
outside the frame that is allocated for them.  The fixture below is a
differential-fuzz case, minimized: original Pancake accepts it, Flapjack
accepts it, and its `main` spills far enough that the two numbers disagree
(the second allocation says 9, the lowered program needs 11).  The check is
the invariant itself, so it stays meaningful if either number changes.
-/

namespace Flapjack.Test.CakeFrameContainment

open Flapjack Flapjack.RiscV Flapjack.Parser

def spillingSource : String :=
    "fun 1 add1(1 a, 1 b) { return a + b; }\n" ++
    "fun {1,1} pair(1 a, 1 b) { return <a, b>; }\n" ++
    "exception E : 1;\n" ++
    "fun 1 main() {\n" ++
    "  var 1 x = 1000;\n" ++
    "  var 1 y115 = add1(((3 | 3) #>> 2), x);\n" ++
    "  var 1 y717 = add1(((y115 #>> 1) << (2 & 2)), (1000 ^ y115));\n" ++
    "  var 1 y98 = add1((ld8 (1000 + 12 + 8)), 0);\n" ++
    "  var 1 y209 = (ld8 1016);\n" ++
    "  var 1 y600 = add1((ld8 1000), (lds 1 (1008)));\n" ++
    "  var {1,1} p938 = pair(y209, y98);\n" ++
    "  try\n" ++
    "    y98 = add1(p938.1, 0)\n" ++
    "  catch E => y600 {\n" ++
    "      while (x > 0) {\n" ++
    "      }\n" ++
    "  }\n" ++
    "  if (p938.0 > ((7 + 1) #>> 7)) {\n" ++
    "    @foo(((lds 1 ((0 + 1000))) << (ld8 (1008 + 1000))), y717, (lds 1 (((0 + 8) + 4))), ((ld8 (1000 + 24 + 1000)) #>> 7));\n" ++
    "  }\n" ++
    "  return add1(((lds 1 (1000 + 12)) ^ (0 & 1)), (p938.1 << p938.0));\n" ++
    "}\n"

/-- The highest frame slot the allocator assigned, and whether any variable
    was placed on the frame at all. -/
def maxAssignedSlot (locations : NatInfoMap WordLocation) : Nat × Bool :=
  locations.foldl
    (fun acc entry =>
      match entry.2 with
      | .stack slot => (max acc.1 slot, true)
      | .register _ => acc)
    (0, false)

/-- Every frame slot the allocator assigns must lie inside the frame the
    pipeline asks Word-to-Stack to allocate, which is
    `if f' = 0 then 0 else f' + 1` words for occupancy `f'`
    (`wordStackCakeFrameSize`). -/
def frameContains (label arity : Nat) (body : WordProg (RiscV.Word 64)) : Bool :=
  let wordParameters := wordSsaAbiParameters arity
  let unallocatedBody := wordRemoveUnreachable (wordProgDCE
    (wordInstSelectProgramFrom
      (wordFuseConditionsAndFold
        (wordConstFp (wordFlattenProgramFrom body)))))
  match CakeRegAlloc.cakeAllocateWordFunctionAfterDead
      label wordParameters unallocatedBody with
  | none => false
  | some (_, _, renamedProgram, allocation) =>
      let slots := cakeWordFrameSlots allocation wordParameters renamedProgram
      let frame := if slots = 0 then 0 else slots + 1
      let (maxSlot, usesFrame) := maxAssignedSlot allocation.locations
      !usesFrame || maxSlot < frame

/-- Cake reserves allocator spill occupancy even when the body has no bitmap
    site (the source `compile_prog` formula has no bitmap-site condition). -/
def spillOnlyFrameOccupancy : Bool :=
  cakeWordFrameSlots
      ({ locations := [], nextSpill := 3 } : WordSpillState)
      [] (WordProg.skip : WordProg (RiscV.Word 64)) == 3

#guard spillOnlyFrameOccupancy

/-! Cake's `format_var` maps even allocator colours below `k` to the
    corresponding abstract register and maps the remaining colours to frame
    slots from the top of the `f`-word frame
    (`word_to_stackScript.sml:114-118`).  This direct guard covers the
    register/frame boundary independently of the emitted bitmap fixtures. -/
def cakeColourLocationOracleExact : Bool :=
  CakeRegAlloc.cakeColourLocation 3 4 0 == .register 0 &&
    CakeRegAlloc.cakeColourLocation 3 4 4 == .register 2 &&
    CakeRegAlloc.cakeColourLocation 3 4 6 == .stack 3 &&
    CakeRegAlloc.cakeColourLocation 3 4 8 == .stack 2

#guard cakeColourLocationOracleExact

/- The actual RISC-V allocator window has `k = 22` Cake stack-register
   colours.  `format_var` keeps colour 42 (register 21) in the ABI window and
   numbers colours 44 and 46 from the top of a five-word frame. -/
def cakeRiscVColourLocationOracleExact : Bool :=
  CakeRegAlloc.cakeColourLocation 22 5 42 == .register 21 &&
    CakeRegAlloc.cakeColourLocation 22 5 44 == .stack 4 &&
    CakeRegAlloc.cakeColourLocation 22 5 46 == .stack 3

#guard cakeRiscVColourLocationOracleExact

/- The direct `compile_prog` frame equation is `MAX nextSpill
   (LENGTH parameters - reg_count)`.  These boundary values pin both
   allocator spill occupancy and Cake's RISC-V argument-frame threshold
   (`reg_count = 22`) independently of the production pipeline. -/
def cakeWordFrameSlotsOracleExact : Bool :=
  let emptyAllocation : WordSpillState := { locations := [], nextSpill := 0 }
  let oneSpill : WordSpillState := { locations := [], nextSpill := 1 }
  let fourSpills : WordSpillState := { locations := [], nextSpill := 4 }
  cakeWordFrameSlots emptyAllocation []
      (WordProg.skip : WordProg (RiscV.Word 64)) == 0 &&
    cakeWordFrameSlots emptyAllocation (List.range 22)
      (WordProg.skip : WordProg (RiscV.Word 64)) == 0 &&
    cakeWordFrameSlots emptyAllocation (List.range 23)
      (WordProg.skip : WordProg (RiscV.Word 64)) == 1 &&
    cakeWordFrameSlots oneSpill (List.range 23)
      (WordProg.skip : WordProg (RiscV.Word 64)) == 1 &&
    cakeWordFrameSlots fourSpills (List.range 23)
      (WordProg.skip : WordProg (RiscV.Word 64)) == 4 &&
    cakeWordFrameSlots emptyAllocation (List.range 25)
      (WordProg.skip : WordProg (RiscV.Word 64)) == 3 &&
    cakeWordFrameSlots emptyAllocation (List.range 26)
      (WordProg.skip : WordProg (RiscV.Word 64)) == 4 &&
    cakeWordFrameSlots oneSpill (List.range 26)
      (WordProg.skip : WordProg (RiscV.Word 64)) == 4

#guard cakeWordFrameSlotsOracleExact

/- The production adapter combines Cake's `total_colour`/`format_var` result
   with the coloured-program `max_var` frame equation.  These two direct
   cases mirror `word_to_stackScript.sml:114-118,586-592`: an in-window
   colour stays a register, while a colour at the first spill boundary is
   addressed from the top of the four-word frame. -/
def cakeColourWordSpillStateOracleExact : Bool :=
  let registerProgram : WordProg Nat := .inst (.const 1 7)
  let registerState := CakeRegAlloc.cakeColourWordSpillState
      2 [] registerProgram [(1, 0)]
  let spillProgram : WordProg Nat := .inst (.const 7 7)
  let spillState := CakeRegAlloc.cakeColourWordSpillState
      2 [] spillProgram [(7, 4)]
  registerState.locations == [(1, .register 0)] &&
    registerState.nextSpill == 0 &&
    spillState.locations == [(7, .stack 1)] &&
    spillState.nextSpill == 3

#guard cakeColourWordSpillStateOracleExact

/-- Cake's `max_var` ignores a handler on a no-return call.  This is distinct
    from the allocator inventory, which must retain the handler for liveness. -/
def cakeMaxVarNoReturnHandler : Bool :=
  wordProgCakeMaxVar
      (.call none none [2]
        (some (54, (.assign 54 (.var 54) : WordProg Nat), 0, 0)) : WordProg Nat) == 2

#guard cakeMaxVarNoReturnHandler

/- The checked Cake word_stack_frame_probe.out reports max_var = 26 for
   two sequential assignments. Keep this source-level frame input distinct
   from the no-return-handler case above. -/
def cakeMaxVarSequenceOracle : Bool :=
  wordProgCakeMaxVar
      (.seq (.assign 0 (.const 0)) (.assign 26 (.const 0)) : WordProg Nat) == 26

#guard cakeMaxVarSequenceOracle

def spillingWordFunctions : Option (List (Nat × Nat × WordProg (RiscV.Word 64))) :=
  match parseTopDecs (BitVec.ofInt 64) spillingSource with
  | .error _ => none
  | .ok declarations =>
      match compileFlapjackEntryCake .rv64i (BitVec.ofNat 64 8)
          (fun value => BitVec.ofNat 64 value) "main"
          (panTargetDeclarationsWithDefaultMain declarations) with
      | none => none
      | some pipeline =>
          some (panToWordCompileProg
            (pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel pipeline.crepe))

/-- The fixture must still reach the back end, or the checks are vacuous. -/
def fixtureReachesBackEnd : Bool :=
  (spillingWordFunctions.map List.length).getD 0 == 4

/-- Every frame slot the allocator assigns lies inside the allocated frame. -/
def frameContainmentExact : Bool :=
  match spillingWordFunctions with
  | none => false
  | some functions =>
      functions.all (fun entry => frameContains entry.1 entry.2.1 entry.2.2)

/-- The fixture must still exercise the frame: at least one of its functions
    has to place a variable there, otherwise `frameContains` holds trivially. -/
def fixtureUsesFrame : Bool :=
  match spillingWordFunctions with
  | none => false
  | some functions =>
      functions.any (fun entry =>
        let wordParameters := wordSsaAbiParameters entry.2.1
        let unallocatedBody := wordRemoveUnreachable (wordProgDCE
          (wordInstSelectProgramFrom
            (wordFuseConditionsAndFold
              (wordConstFp (wordFlattenProgramFrom entry.2.2)))))
        match CakeRegAlloc.cakeAllocateWordFunctionAfterDead
            entry.1 wordParameters unallocatedBody with
        | none => false
        | some (_, _, _, allocation) => (maxAssignedSlot allocation.locations).2)

#guard fixtureReachesBackEnd

#guard frameContainmentExact

#guard fixtureUsesFrame

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("the frame-containment fixture still reaches the Word back end",
        fixtureReachesBackEnd),
      ("the frame-containment fixture still spills to the frame",
        fixtureUsesFrame),
      ("bitmap-free allocator spills retain Cake frame occupancy",
        spillOnlyFrameOccupancy),
      ("Cake colour locations match format_var register/frame slots",
        cakeColourLocationOracleExact),
      ("RISC-V Cake colours cross the k=22 frame boundary",
        cakeRiscVColourLocationOracleExact),
      ("cakeWordFrameSlots matches the direct Cake frame equation",
        cakeWordFrameSlotsOracleExact),
      ("Cake colour-to-spill adapter matches format_var and frame sizing",
        cakeColourWordSpillStateOracleExact),
      ("Cake max_var preserves the sequential-assignment frame input",
        cakeMaxVarSequenceOracle),
      ("allocator frame slots stay inside the frame word_to_stack allocates",
        frameContainmentExact) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeFrameContainment
