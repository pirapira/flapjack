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
    stackFree (.inl 3) 15 12 20 19 == 17 &&
    stackFree (.inr 3) 15 12 20 19 == 18 &&
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

/- The RISC-V Cake ABI has `k = 22` allocator registers.  These rows are the
   direct `compile_prog` reservation at the real argument-area boundary: no
   overflow at 22 words, one overflow at 23, and the frame's extra link word
   is retained while the argument area grows at 24 and 26 words.  The
   `wide_call_arity.pnk` oracle exercises the same accepted source boundary;
   this guard pins the intermediate `f - stack_arg_count` arithmetic. -/
def riscvFrameReservationBoundaryExact : Bool :=
  wordStackFrameWords (List.range 22) 22 0 == 0 &&
    wordStackFrameWords (List.range 23) 22 1 == 1 &&
    wordStackFrameWords (List.range 24) 22 2 == 1 &&
    wordStackFrameWords (List.range 26) 22 4 == 1

#guard riscvFrameReservationBoundaryExact

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

/- Cake's direct `num_stack_ret 22 vs` row is one stack slot for a 22-word
   `vs`: the separate `v1` consumes the final ABI result position.  The
   flattened Word-to-Stack boundary must preserve that same `+1`, both for
   the frame free count and for the returned-call copy suffix. -/
def wideReturnFrameBoundaryExact : Bool :=
  let config : WordStackConfig :=
    { locations := [], scratch := 31, stackBase := 0,
      abiRegisterCount := 22, abiFrameSlots := 12 }
  stackNumReturnSlots 22 (List.range 22) == 1 &&
    wordStackReturnFreeCount config (List.range 22) == 12 &&
    wordStackReturnStackSuffix config (List.range 22) == [21]

#guard wideReturnFrameBoundaryExact

/- Cake's `copy_ret` copies stack-resident return values in descending frame
   order, then frees exactly the temporary return slots.  These two shapes
   are the direct `copy_ret_handler_2`/multi-value rows from
   `word_stack_call_probe.out`; keeping them here covers the frame boundary
   used by both ordinary returns and handler returns. -/
def returnCopyCakeGuard : Bool :=
  match stackCopyReturn (α := Nat) false false 1 31 4 [10, 12]
      (.skip : StackProg Nat) with
  | .seq
      (.seq (.stackLoad 31 1)
        (.seq (.stackStore 31 5)
          (.seq (.stackLoad 31 0)
            (.seq (.stackStore 31 4) .skip))))
      (.seq (.stackFree 2) .skip) => true
  | _ => false

#guard returnCopyCakeGuard

def handlerReturnCopyCakeGuard : Bool :=
  match stackCopyReturn (α := Nat) true true 1 31 4 [10]
      (.skip : StackProg Nat) with
  | .seq
      (.seq (.stackLoad 31 0)
        (.seq (.stackStore 31 9) .skip))
      (.seq (.stackFree 1) .skip) => true
  | _ => false

#guard handlerReturnCopyCakeGuard

/- These are the canonical `word_stack_call_probe.out` rows, including the
   handler-frame offset used by Cake's `copy_ret F T (2,6,5) [4;6;8]`. -/
def copyRetProbeRowsCakeGuard : Bool :=
  stackNumReturnSlots 12 [4, 6, 8] == 0 &&
    stackNumReturnSlots 2 [4, 6, 8] == 2 &&
    (match stackCopyReturn (α := Nat) false false 12 20 19 [4, 6, 8]
        (.skip : StackProg Nat) with
     | .skip => true
     | _ => false) &&
    (match stackCopyReturn (α := Nat) false true 2 2 6 [4, 6, 8]
        (.skip : StackProg Nat) with
     | .seq
         (.seq (.stackLoad 2 1)
           (.seq (.stackStore 2 10)
             (.seq (.stackLoad 2 0)
               (.seq (.stackStore 2 9) .skip))))
         (.seq (.stackFree 2) .skip) => true
     | _ => false)

#guard copyRetProbeRowsCakeGuard

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

/- `StackArgs` rows from `word_stack_call_probe.out`: direct calls count the
   target slot while indirect calls do not, and both copy overflow arguments
   from the caller frame at its Cake `f` offset. -/
def stackArgsMatchesCakeProbe : Bool :=
  let emptyOk :=
    match (stackArgs (α := Nat) 0 6 3) with
    | .stackAlloc words => words == 0
    | _ => false
  let directOk :=
    match (stackArgs (α := Nat) 2 6 3) with
    | .seq
        (.seq (.stackAlloc words)
          (.seq (.stackLoad loadOne loadOffsetOne)
            (.stackStore storeOne storeOffsetOne)))
        (.seq (.stackLoad loadZero loadOffsetZero)
          (.stackStore storeZero storeOffsetZero)) =>
        words == 2 && loadOne == 3 && loadOffsetOne == 7 &&
          storeOne == 3 && storeOffsetOne == 1 && loadZero == 3 &&
          loadOffsetZero == 6 && storeZero == 3 && storeOffsetZero == 0
    | _ => false
  let indirectOk :=
    match (stackArgs (α := Nat) 1 6 3) with
    | .seq (.stackAlloc words)
        (.seq (.stackLoad loadRegister loadOffset)
          (.stackStore storeRegister storeOffset)) =>
        words == 1 && loadRegister == 3 && loadOffset == 6 &&
          storeRegister == 3 && storeOffset == 0
    | _ => false
  emptyOk && directOk && indirectOk

#guard stackArgsMatchesCakeProbe

/- Cake's direct `StackHandlerArgs F (INL 0) 3 (12,20,19)` row has no
   stack-resident arguments: `stack_arg_count` is zero before the handler's
   three reserved slots are added to the frame. -/
def stackHandlerArgsMatchesCakeProbe : Bool :=
  match (stackHandlerArgs (α := Nat) false 0 20 12) with
  | .stackAlloc words => words == 0
  | _ => false

#guard stackHandlerArgsMatchesCakeProbe

/- The direct `call_dest (SOME target)` path keeps the target as a label and
   does not add a frame-free instruction when Cake's computed free count is
   zero for an empty frame. -/
def directCallDestinationCakeGuard : Bool :=
  match wordToStackProgNat
      { locations := [], scratch := 31, stackBase := 0 }
      (.call none (some 7) [] none : WordProg Nat) with
  | some (.call none (.label target) none) => target == 7
  | _ => false

#guard directCallDestinationCakeGuard

/- Cake's returning direct-call wrapper includes the implicit return slot in
   `StackArgs`, preserves the return-handler labels, and retains its explicit
   zero `StackFree` tail. -/
def returningCallCarrierCakeGuard : Bool :=
  match wordToStackCallNoHandler (α := Nat) false 7 0 6 3 []
      (.skip : StackProg Nat) 20 21 with
  | .seq
      (.seq (.stackAlloc words)
        (.seq (.stackLoad loadRegister loadOffset)
          (.stackStore storeRegister storeOffset)))
      (.seq (.call (some (.skip, freeFrame, returnLabel, entryLabel))
          (.label target) none)
        (.stackFree freeWords)) =>
      words == 1 && loadRegister == 3 && loadOffset == 6 &&
        storeRegister == 3 && storeOffset == 0 && freeFrame == 0 &&
        returnLabel == 20 && entryLabel == 21 && target == 7 &&
        freeWords == 0
  | _ => false

#guard returningCallCarrierCakeGuard

def containsHandlerCallCakeShape : StackProg Nat → Bool
  | .call (some (_, freeFrame, returnLabel, entryLabel)) (.label target)
      (some (_, exceptionLabel, handlerEntryLabel)) =>
      freeFrame == 0 && returnLabel == 20 && entryLabel == 21 &&
        target == 7 && exceptionLabel == 40 && handlerEntryLabel == 31
  | .seq first second =>
      containsHandlerCallCakeShape first || containsHandlerCallCakeShape second
  | _ => false

/- Cake's handler-call carrier keeps the target and all three label carriers in
   the final call node after the handler setup and argument prefix. -/
def handlerCallCarrierCakeGuard : Bool :=
  containsHandlerCallCakeShape
    (wordToStackCallWithHandlerInSection (α := Nat) false 7 0 6 3
      (.skip : StackProg Nat) (.raise 4) 20 21 30 31 40)

#guard handlerCallCarrierCakeGuard

/-! The real Cake RISC-V ABI window has twelve value slots.  At the exact
    boundary, `format_var` keeps index 11 in the last ABI register and
    `wMoveSingle` places indices 12 and 13 at the top two slots of the
    caller's four-word frame. -/
def riscvAbiBoundaryPhysicalLocationsExact : Bool :=
  let config : WordStackConfig :=
    { locations := [], scratch := 22, stackBase := 0,
      abiRegisterCount := 12, abiFrameSlots := 3, frameOffset := 4 }
  wordStackPhysicalLocation config 11 1 == .register 23 &&
    wordStackPhysicalLocation config 12 1 == .stack 3 &&
    wordStackPhysicalLocation config 13 1 == .stack 2

#guard riscvAbiBoundaryPhysicalLocationsExact

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("stack_arg_count and stack_free match the call oracle", callArgCountExact),
      ("SeqStackFree matches the port's tail-call frame free", seqStackFreeExact),
      ("wordStackFrameWords matches compile_prog's frame reservation",
        frameReservationExact),
      ("RISC-V frame reservation crosses Cake's k=22 boundary",
        riscvFrameReservationBoundaryExact),
      ("wordStackCallFreeCount matches stack_free for direct calls",
        callFrameFreeCountExact),
      ("source-shaped tail calls include the Cake link slot",
        sourceTailCallFreeCountExact),
      ("returns free the Cake current frame after ABI moves",
        returnFrameFreeExact),
      ("wide returns retain Cake's implicit v1 return slot",
        wideReturnFrameBoundaryExact),
      ("copy_ret preserves Cake multi-value return frame order",
        returnCopyCakeGuard),
      ("copy_ret preserves Cake handler-frame return layout",
        handlerReturnCopyCakeGuard),
      ("copy_ret and num_stack_ret match Cake's direct probe rows",
        copyRetProbeRowsCakeGuard),
      ("indirect calls take a register target from the last argument",
        indirectRegisterTargetExact),
      ("indirect calls load a stack target through scratch",
        indirectStackTargetExact),
      ("an indirect call without arguments falls back to the raise stub",
        indirectEmptyTargetExact),
      ("StackArgs uses compile_prog's caller frame size f",
        callFrameOffsetMatchesCakeF),
      ("an overflow argument sits at wMoveSingle's f - 1 - (r - k)",
        overflowArgumentSlotMatchesWMoveSingle),
      ("StackArgs direct/indirect shapes match Cake's probe",
        stackArgsMatchesCakeProbe),
      ("StackHandlerArgs matches Cake's direct handler probe",
        stackHandlerArgsMatchesCakeProbe),
      ("direct call destination preserves Cake's label carrier",
        directCallDestinationCakeGuard),
      ("returning direct call preserves Cake's carrier shape",
        returningCallCarrierCakeGuard),
      ("handler call preserves Cake's carrier metadata",
        handlerCallCarrierCakeGuard),
      ("the RISC-V ABI boundary uses Cake's first two spill slots",
        riscvAbiBoundaryPhysicalLocationsExact) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.WordStackCallParity
