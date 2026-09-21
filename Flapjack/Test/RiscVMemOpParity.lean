import Flapjack.RiscV.Backend

/-! Direct target parity for Cake's riscv_memop mapping from
    compiler/encoders/riscv/riscv_targetScript.sml:68-74.  The checked HOL
    output is in scripts/hol-probes/riscv_target_memop_probe.out; the
    corresponding Flapjack boundary is wordInstToInstruction. -/

namespace Flapjack.Test.RiscVMemOpParity

open Flapjack
open Flapjack.RiscV

def load32Guard : Bool :=
  wordInstToInstruction (width := 64) (.mem .load32 4 5) ==
    some (.load32 4 5)

def load16Guard : Bool :=
  wordInstToInstruction (width := 64) (.mem .load16 4 5) ==
    some (.loadHalf 4 5)

def load8Guard : Bool :=
  wordInstToInstruction (width := 64) (.mem .load8 4 5) ==
    some (.loadByte 4 5)

def loadGuard : Bool :=
  wordInstToInstruction (width := 64) (.mem .load 4 5) ==
    some (.loadWord 4 5)

def store32Guard : Bool :=
  wordInstToInstruction (width := 64) (.mem .store32 4 5) ==
    some (.store32 4 5)

def store16Guard : Bool :=
  wordInstToInstruction (width := 64) (.mem .store16 4 5) ==
    some (.storeHalf 4 5)

def store8Guard : Bool :=
  wordInstToInstruction (width := 64) (.mem .store8 4 5) ==
    some (.storeByte 4 5)

def storeGuard : Bool :=
  wordInstToInstruction (width := 64) (.mem .store 4 5) ==
    some (.storeWord 4 5)

def parityGuard : Bool :=
  load32Guard && load16Guard && load8Guard && loadGuard &&
    store32Guard && store16Guard && store8Guard && storeGuard

#guard load32Guard
#guard load16Guard
#guard load8Guard
#guard loadGuard
#guard store32Guard
#guard store16Guard
#guard store8Guard
#guard storeGuard
#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("riscv_memop Load32 maps to Cake LWU", load32Guard),
      ("riscv_memop Load16 maps to Cake LHU", load16Guard),
      ("riscv_memop Load8 maps to Cake LBU", load8Guard),
      ("riscv_memop Load maps to Cake LD", loadGuard),
      ("riscv_memop Store32 maps to Cake SW", store32Guard),
      ("riscv_memop Store16 maps to Cake SH", store16Guard),
      ("riscv_memop Store8 maps to Cake SB", store8Guard),
      ("riscv_memop Store maps to Cake SD", storeGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.RiscVMemOpParity
