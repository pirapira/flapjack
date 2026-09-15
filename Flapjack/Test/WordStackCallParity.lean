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

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("stack_arg_count and stack_free match the call oracle", callArgCountExact),
      ("SeqStackFree matches the port's tail-call frame free", seqStackFreeExact),
      ("wordStackFrameWords matches compile_prog's frame reservation",
        frameReservationExact),
      ("wordStackCallFreeCount matches stack_free for direct calls",
        callFrameFreeCountExact),
      ("indirect calls take a register target from the last argument",
        indirectRegisterTargetExact),
      ("indirect calls load a stack target through scratch",
        indirectStackTargetExact),
      ("an indirect call without arguments falls back to the raise stub",
        indirectEmptyTargetExact) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.WordStackCallParity
