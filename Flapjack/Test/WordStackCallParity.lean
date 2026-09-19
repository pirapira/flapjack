import Flapjack.RiscV.CakeAllocatorCore
import Flapjack.RiscV.WordToStack

/-!
# CakeML Word-to-Stack frame and call parity checks

The expected values are direct EVAL observations from
`word_stack_call_probe.out`, which evaluates the original
`word_to_stackScript.sml` definitions `call_dest`, `stack_arg_count`,
`stack_free`, `StackArgs`, `SeqStackFree`, `copy_ret`, and `compile_prog`.

This module pins the port's frame-size and call-lowering boundary (bead
flapjack-2ib / GH #1047): the frame reservation matches Cake's
`f - stack_arg_count`, direct tail calls free the caller frame like
`SeqStackFree`, and indirect calls read their target from the last argument
exactly as `call_dest NONE` does.
-/

namespace Flapjack.Test.WordStackCallParity

open Flapjack
open Flapjack.RiscV
open Flapjack.RiscV.CakeAlloc

/-! `stack_arg_count` and `stack_free` on the fresh probe configuration
    `(k, f, f') = (3, 6, 5)`; the direct case counts the target slot, the
    indirect case does not. -/
def callArgCountExact : Bool :=
  stackArgCount (.inl 3) 15 12 == 3 &&
    stackArgCount (.inr 3) 15 12 == 2 &&
    stackArgCount (.inl 0) 5 3 == 2 &&
    stackArgCount (.inr 0) 5 3 == 1 &&
    stackFree (.inl 0) 5 3 6 5 == 4 &&
    stackFree (.inr 0) 5 3 6 5 == 5

#guard callArgCountExact

/-! `SeqStackFree` only emits a `StackFree` for a nonzero count, matching the
    port's `stackFreeIfNonzero`. -/
def seqStackFreeExact : Bool :=
  (match stackFreeIfNonzero 0 (.skip : StackProg Nat) with
   | .skip => true
   | _ => false) &&
    (match stackFreeIfNonzero 2 (.skip : StackProg Nat) with
     | .seq (.stackFree 2) .skip => true
     | _ => false)

#guard seqStackFreeExact

/-! `compile_prog` frame sizes observed by the probe: `f` and the entry
    `StackAlloc (f - stack_arg_count)`.  The port's `wordStackFrameWords`
    reproduces the reservation for the same `(arg_count, reg_count, f')`. -/
def frameReservationExact : Bool :=
  wordStackFrameWords (List.range 15) 12 3 == 1 &&
    wordStackFrameWords (List.range 5) 3 2 == 1 &&
    wordStackFrameWords (List.range 3) 3 0 == 0 &&
    wordStackFrameWords (List.range 3) 3 11 == 12

#guard frameReservationExact

def callFrameFreeCountExact : Bool :=
  wordStackCakeFrameSize
      { locations := [], scratch := 31, stackBase := 0, abiFrameSlots := 19 } == 20 &&
    wordStackCallFreeCount
      { locations := [], scratch := 31, stackBase := 0,
        abiFrameSlots := 19, abiRegisterCount := 12 } 15 == 17 &&
    wordStackCallFreeCount
      { locations := [], scratch := 31, stackBase := 0,
        abiFrameSlots := 19, abiRegisterCount := 12 } 8 == 20

#guard callFrameFreeCountExact

/-! Source-shaped `loop_to_word` calls carry Cake's link slot in their Word
    argument list.  Cake's direct-tail `stack_free` still uses the direct-call
    `stack_arg_count` formula, so an argument list below the ABI window frees
    the complete current frame. -/
def sourceTailCallFreeCountExact : Bool :=
  wordStackSourceTailCallFreeCount
      { locations := [], scratch := 31, stackBase := 0, abiFrameSlots := 5 } 5 == 6 &&
    wordStackSourceTailCallFreeCount
      { locations := [], scratch := 31, stackBase := 0, abiFrameSlots := 5 } 4 == 6

#guard sourceTailCallFreeCountExact

/-! Cake's `comp Return` frees a non-empty current frame after moving the
    returned ABI values.  The source-shaped port keeps `v1` in the values list,
    so one returned value in a two-word frame still frees both frame words. -/
def returnFrameFreeExact : Bool :=
  wordStackReturnFreeCount
      { locations := [(0, .register 5)], scratch := 31, stackBase := 0,
        abiFrameSlots := 1 } [0] == 2 &&
    match (wordStackReturn
        { locations := [(0, .register 5)], scratch := 31, stackBase := 0,
          abiFrameSlots := 1 } 0 [0] : Option (StackProg Nat)) with
    | some (.seq (.arith .or 1 5 5)
        (.seq (.stackFree 2) (.return 5))) => true
    | _ => false

#guard returnFrameFreeExact

/-! Indirect-call targets follow `call_dest NONE`: the last argument names the
    target, a register-resident target is used directly, a stack-resident one
    is loaded into `scratch`, and the remaining arguments are the formals. -/
def indirectRegisterTargetExact : Bool :=
  match wordStackIndirectCallNat
      { locations := [(8, .register 4)], scratch := 13, stackBase := 0 } [4, 6, 8] with
  | some ([4, 6], .register 4, .skip) => true
  | _ => false

#guard indirectRegisterTargetExact

def indirectStackTargetExact : Bool :=
  match wordStackIndirectCallNat
      { locations := [(26, .stack 18)], scratch := 13, stackBase := 0 } [4, 6, 26] with
  | some ([4, 6], .register 13, .stackLoad 13 18) => true
  | _ => false

#guard indirectStackTargetExact

def indirectEmptyTargetExact : Bool :=
  match wordStackIndirectCallNat
      { locations := [], scratch := 13, stackBase := 0 } [] with
  | some ([], .label label, .skip) => label == stackRaiseStubLocation
  | _ => false

#guard indirectEmptyTargetExact

/-! `StackArgs dest arg_count (k,f,f') = stack_move n 0 f k (StackAlloc n)`
    (`word_to_stackScript.sml:287-292`), and `stack_move` reads its source at
    `start + f`, where `f` is the *caller's* frame size -- Cake's
    `compile_prog` `f`, not the public `stack_var_count` occupancy `f'`.
    `wordStackCallFrameOffset` is the port's `f`, so pin it against
    `compile_prog`'s `f = if stack_var_count = 0 then 0 else
    stack_var_count + 1`.  Getting this wrong loads the overflow argument
    from the allocator's own slot instead of the caller frame, which is bead
    flapjack-pxn.8.5.14.17. -/
def callFrameOffsetMatchesCakeF : Bool :=
  let frameless : WordStackConfig :=
    { locations := [], scratch := 22, stackBase := 0,
      abiFrameSlots := 0, frameOffset := 0 }
  let occupied : Nat → WordStackConfig := fun occupancy =>
    { locations := [], scratch := 22, stackBase := 0,
      abiFrameSlots := occupancy, frameOffset := occupancy + 1 }
  wordStackCallFrameOffset frameless == 0 &&
    ((List.range 12).all (fun occupancy =>
      wordStackCallFrameOffset (occupied (occupancy + 1)) == occupancy + 2))

/-! `wMoveSingle` materializes an overflow argument at `f - 1 - (r - k)`
    (`word_to_stackScript.sml`), counting down from the top of the caller
    frame.  `wordStackPhysicalLocation` is that formula. -/
def overflowArgumentSlotMatchesWMoveSingle : Bool :=
  let config : WordStackConfig :=
    { locations := [], scratch := 22, stackBase := 0,
      abiRegisterCount := 22, abiFrameSlots := 9, frameOffset := 10 }
  -- `f` is 10 here, so index 22 is slot 9, index 23 slot 8, and so on.
  [(22, 9), (23, 8), (24, 7), (25, 6)].all (fun entry =>
    match wordStackPhysicalLocation config entry.1 1 with
    | .stack slot => slot == entry.2
    | _ => false)

#guard callFrameOffsetMatchesCakeF
#guard overflowArgumentSlotMatchesWMoveSingle

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("stack_arg_count and stack_free match the call oracle", callArgCountExact),
      ("SeqStackFree matches the port's tail-call frame free", seqStackFreeExact),
      ("wordStackFrameWords matches compile_prog's frame reservation",
        frameReservationExact),
      ("wordStackCallFreeCount matches stack_free for direct calls",
        callFrameFreeCountExact),
      ("source-shaped tail calls include the Cake link slot",
        sourceTailCallFreeCountExact),
      ("returns free the Cake current frame after ABI moves",
        returnFrameFreeExact),
      ("indirect calls take a register target from the last argument",
        indirectRegisterTargetExact),
      ("indirect calls load a stack target through scratch",
        indirectStackTargetExact),
      ("an indirect call without arguments falls back to the raise stub",
        indirectEmptyTargetExact),
      ("StackArgs uses compile_prog's caller frame size f",
        callFrameOffsetMatchesCakeF),
      ("an overflow argument sits at wMoveSingle's f - 1 - (r - k)",
        overflowArgumentSlotMatchesWMoveSingle) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.WordStackCallParity
