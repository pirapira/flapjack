import Flapjack.RiscV.CakeAllocatorCore

/-!
# CakeML Word-to-Stack frame policy checks

The expected values are direct EVAL observations from
`word_stack_frame_probe.out`, covering frame spill slots, temporary
numbering, call-stack occupancy, and bitmap word encoding.
-/

namespace Flapjack.Test.CakeFramePolicy

open Flapjack.RiscV.CakeAlloc

def registerFrameExact : Bool :=
  wReg1 4 12 20 19 == ([], 2) &&
    wReg1 24 12 20 19 == ([(12, 19)], 12) &&
    wReg1 25 12 20 19 == ([(12, 19)], 12) &&
    wReg1 26 12 20 19 == ([(12, 18)], 12) &&
    wReg2 4 12 20 19 == ([], 2) &&
    wReg2 26 12 20 19 == ([(13, 18)], 13)

#guard registerFrameExact

def formatExact : Bool :=
  formatVar 12 (some 4) == .register 4 &&
    formatVar 12 (some 26) == .stack 26 &&
    formatVar 12 none == .register 13

#guard formatExact

def callFrameExact : Bool :=
  stackArgCount (.inl 3) 15 12 == 3 &&
    stackArgCount (.inr 3) 15 12 == 2 &&
    stackFree (.inl 3) 8 12 20 19 == 20 &&
    stackFree (.inr 3) 15 12 20 19 == 18

#guard callFrameExact

def bitmapEncodingExact : Bool :=
  bitsToWord [true, false, true] == 5 &&
    bitsToWord [false, false, false] == 0 &&
    frameBitmapWords 3 [true, false, true, false, true] == [13, 2] &&
    writeBitmap [] 12 3 64 == [8] &&
    writeBitmap [24] 12 3 64 == [12] &&
    writeBitmap [25, 26] 12 3 64 == [14]

#guard bitmapEncodingExact

def temporaryNumberingExact : Bool :=
  limitVar 0 == 5 && limitVar 26 == 29

#guard temporaryNumberingExact

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("wReg1/wReg2 preserve Cake frame slot numbering", registerFrameExact),
      ("format_var preserves register and spilled alternatives", formatExact),
      ("stack_arg_count and stack_free preserve call occupancy", callFrameExact),
      ("bits_to_word and write_bitmap preserve Cake bitmap words",
        bitmapEncodingExact),
      ("limit_var preserves the SSA temporary numbering base",
        temporaryNumberingExact) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeFramePolicy
