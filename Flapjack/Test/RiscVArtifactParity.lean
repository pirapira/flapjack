import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.Test.OriginalPancakeProbes

/-!
# Exact RISC-V artifact parity for the `dec_clock` fixture

`Flapjack/Test/OriginalPancake/dec_clock.pnk` is

```
fun 1 main() { tick; return 7; }
```

The original CakeML Pancake compiler and the Flapjack port both accept this
program and both place `cml_generated_main` at byte offset 1000 and `cml_main`
at byte offset 1004 inside the `cake_main` frame.  This module pins the exact
generated artifact sections of both compilers in the same
`(label, base, bytes)` format used by `scripts/parity-small-corpus.py`, so the
comparison is on instruction and data bytes plus layout metadata rather than
on mere compiler acceptance.

A second fixture, `Flapjack/Test/OriginalPancake/const_return.pnk`, is

```
fun 1 main() { return 7; }
```

The original compiler produces byte-identical output for this no-tick program
and for the `dec_clock` program (same SHA-256 and same 8-byte terminal
`addi a0,x0,7; ret`), so the original drops the standalone `Tick`.  The port
instead emits one `tick` nop, so the `dec_clock` `cml_main` is exactly the
no-tick `cml_main` prefixed by that single nop.  This isolation is checked
below; the no-tick residual mismatch is likewise tracked by
`flapjack-pxn.8.5.10.1`.

The original-side facts are the `OriginalPancakeProbes.decClock` source-backed
probe, whose dependency is the direct HOL probe
`scripts/hol-probes/pan_sem_dec_clock_e2e_probeScript.sml`.  That probe
evaluates the original `panSem$evaluate` on `tick; return 7` and observes
`SOME (Return (ValWord 7w))` with the clock decremented from `5` to `4`, which
is the semantic result the generated artifact must implement.

The generated `cml_generated_main` section is byte-identical.  The generated
`cml_main` sections are not: the original emits the 8-byte constant return
`addi a0,x0,7; ret`, while the port emits 16 bytes because it lowers `tick`
and the return move through its typed pipeline.  That residual mismatch is the
reproducible, tracked gap owned by `flapjack-pxn.8.5.10.1`; it is recorded
exactly here instead of being weakened to an acceptance check.
-/

namespace Flapjack.Test.RiscVArtifactParity

open Flapjack Flapjack.RiscV
open Flapjack.Test.OriginalPancakeProbes (decClock constReturn)

/-- The checked source-facing pipeline configuration used by the compiler
entry point, kept local so this parity test does not import the executable
`CompileMain` module and collide with the test driver's `main`. -/
def artifactCompileConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 20
    bytesInWord := 8
    stackBase := 21
    wordShift := 3 }

/-- The fixture source, taken from the original-side probe fact so the two
comparisons cannot drift apart. -/
def decClockSource : String := decClock.source

/-- Original CakeML `cml_generated_main` bytes: the 4-byte direct jump to
`cml_main`. -/
def cakeGeneratedMainBytes : List (BitVec 8) :=
  [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)

/-- Original CakeML `cml_main` bytes: `addi a0,x0,7; ret`. -/
def cakeMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x70, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Flapjack `cml_generated_main` bytes, identical to the original. -/
def flapjackGeneratedMainBytes : List (BitVec 8) :=
  [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)

/-- Flapjack `cml_main` bytes: the 16-byte tick-then-return-lowering shape
tracked by `flapjack-pxn.8.5.10.1`. -/
def flapjackMainBytes : List (BitVec 8) :=
  [0x13, 0x00, 0x00, 0x00,
   0x13, 0x01, 0x70, 0x00,
   0x33, 0x61, 0x21, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Run a source program through the production runtime-image entry point,
which is the exact path `flapjack-compile --assembly` uses. -/
def compileRuntimeImage (source : String) :
    Option (SourceRiscVRuntimeImage 64) :=
  match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] artifactCompileConfig
      "main" source with
  | .ok image => some image
  | .error _ => none

/-- The emitted sections (labels `≥ 3`) with the `makesym` base offsets that
`RiscV.pancakeRuntimeAssembly` assigns cumulatively from `1000`.  The lower
labels are the internal port runtime and are not emitted. -/
def emittedSections (image : SourceRiscVRuntimeImage 64) :
    List (Nat × Nat × List (BitVec 8)) :=
  let rec go (offset : Nat) (sections : List (EncodedRiscVSection 64)) :
      List (Nat × Nat × List (BitVec 8)) :=
    match sections with
    | [] => []
    | sec :: rest =>
        if sec.label < 3 then go offset rest
        else (sec.label, offset, sec.bytes) ::
          go (offset + sec.bytes.length) rest
  go 1000 image.sections

/-- Exact emitted `(label, base, bytes)` artifact for the fixture. -/
def decClockEmittedSections : List (Nat × Nat × List (BitVec 8)) :=
  match compileRuntimeImage decClockSource with
  | some image => emittedSections image
  | none => []

/-- The runtime-image entry point accepts the fixture and exposes the five
encoded sections and no static warnings. -/
def artifactAccepted : Bool :=
  match compileRuntimeImage decClockSource with
  | some image => image.sections.length == 5 && image.warnings.isEmpty
  | none => false

/-- The generated initializer section is byte-identical across the compilers. -/
def generatedMainBytesMatch : Bool :=
  cakeGeneratedMainBytes == flapjackGeneratedMainBytes

/-- The port lays out the two emitted sections exactly as the original does:
`cml_generated_main` at base 1000 and `cml_main` at base 1004. -/
def emittedLayoutMatches : Bool :=
  decClockEmittedSections ==
    [ (3, 1000, flapjackGeneratedMainBytes),
      (4, 1004, flapjackMainBytes) ]

/-- The port's bitmap table for the fixture is the initial single word `[4]`. -/
def bitmapsMatch : Bool :=
  match compileRuntimeImage decClockSource with
  | some image => image.bitmaps.data == [4]
  | none => false

/-- The residual `cml_main` mismatch, recorded with its exact bytes and owner
rather than accepted: the original emits 8 bytes, the port 16, both terminate
in the same `ret` word, and the original source-backed probe pins that word. -/
def trackedMainMismatch : Bool :=
  cakeMainBytes != flapjackMainBytes &&
    cakeMainBytes.length == 8 && flapjackMainBytes.length == 16 &&
    cakeMainBytes.drop (cakeMainBytes.length - 4) == decClock.cakeFinalBytes &&
    flapjackMainBytes.drop (flapjackMainBytes.length - 4) ==
      decClock.cakeFinalBytes

/-- The `const_return` fixture source: the no-tick counterpart to
`dec_clock`, taken from the original-side probe fact. -/
def constReturnSource : String := constReturn.source

/-- Flapjack `cml_main` bytes for the no-tick `return 7` fixture: the 12-byte
`addi x2,x0,7; or x2,x2,x2; ret` shape.  Its difference from `dec_clock` is
exactly the single leading `tick` nop, which is the residual gap isolated
below. -/
def flapjackConstReturnMainBytes : List (BitVec 8) :=
  [0x13, 0x01, 0x70, 0x00,
   0x33, 0x61, 0x21, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- The single 4-byte `tick` lowering emitted by the port: `addi x0,x0,0`. -/
def standaloneTickNop : List (BitVec 8) :=
  [0x13, 0x00, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Exact emitted `(label, base, bytes)` artifact for the `const_return`
fixture. -/
def constReturnEmittedSections : List (Nat × Nat × List (BitVec 8)) :=
  match compileRuntimeImage constReturnSource with
  | some image => emittedSections image
  | none => []

/-- The port lays out the two emitted sections exactly as it does for
`dec_clock`: `cml_generated_main` at base 1000 and `cml_main` at base 1004. -/
def constReturnLayoutMatches : Bool :=
  constReturnEmittedSections ==
    [ (3, 1000, flapjackGeneratedMainBytes),
      (4, 1004, flapjackConstReturnMainBytes) ]

/-- The `dec_clock` `cml_main` differs from the no-tick `const_return` shape
by exactly one leading `tick` nop, isolating the standalone-`Tick` gap. -/
def standaloneTickIsolated : Bool :=
  flapjackMainBytes == standaloneTickNop ++ flapjackConstReturnMainBytes

/-- The residual no-tick `cml_main` mismatch, recorded with its exact bytes
and owner: the original emits 8 bytes, the port 12, both terminate in the same
`ret` word, and the source-backed `const_return` probe pins that word.  The
original bytes are byte-identical to the `dec_clock` original, evidencing that
the original drops the standalone `Tick`. -/
def trackedConstReturnMismatch : Bool :=
  cakeMainBytes != flapjackConstReturnMainBytes &&
    cakeMainBytes.length == 8 && flapjackConstReturnMainBytes.length == 12 &&
    cakeMainBytes.drop (cakeMainBytes.length - 4) ==
      constReturn.cakeFinalBytes &&
    flapjackConstReturnMainBytes.drop (flapjackConstReturnMainBytes.length - 4) ==
      constReturn.cakeFinalBytes

#guard artifactAccepted
#guard generatedMainBytesMatch
#guard emittedLayoutMatches
#guard bitmapsMatch
#guard trackedMainMismatch
#guard constReturnLayoutMatches
#guard standaloneTickIsolated
#guard trackedConstReturnMismatch

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("dec_clock fixture accepted by the runtime-image entry point",
        artifactAccepted),
      ("dec_clock original and port generated initializer bytes match",
        generatedMainBytesMatch),
      ("dec_clock emitted section layout matches the original bases",
        emittedLayoutMatches),
      ("dec_clock bitmap table is the initial [4]",
        bitmapsMatch),
      ("dec_clock residual cml_main mismatch is tracked, not accepted",
        trackedMainMismatch),
      ("const_return emitted section layout matches the original bases",
        constReturnLayoutMatches),
      ("dec_clock cml_main isolates a single standalone tick nop",
        standaloneTickIsolated),
      ("const_return residual cml_main mismatch is tracked, not accepted",
        trackedConstReturnMismatch) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.RiscVArtifactParity
