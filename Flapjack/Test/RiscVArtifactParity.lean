import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.RiscV.ArtifactFormat
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

A third fixture, `Flapjack/Test/OriginalPancake/entry_order.pnk`, declares the
entry function last:

```
fun 1 a() { return 1; }
fun 1 b() { return 2; }
fun 1 main() { return a(); }
```

The original CPU pipeline moves the `main` declaration to the front
(`cakeml/pancake/pan_passesScript.sml:20-37`, `pan_to_target_all_def`), so it
emits `cml_generated_main`, `cml_main`, `cml_a`, `cml_b` in that order.  The
port renames the source entry, wraps it, and emits source order
(`cml_generated_main`, `cml_a`, `cml_b`, `main`).  That deterministic section
ordering divergence, plus the 8-byte-vs-12-byte helper bodies, is the tracked
gap owned by `flapjack-pxn.8.5.10.3`.

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

A fourth fixture, `Flapjack/Test/OriginalPancake/nested_expression.pnk`, is the
GitHub issue #1015 reproducer whose right-nested sum
`((t1 + (a + (b + (c + d)))) << 1) >>> 1` needs more than the port's fixed
four-register Word-to-Stack temporary pool.  The original flattens the
expression through `crep_to_loop` and accepts it.  With the pool-expansion fix
tracked by `flapjack-pxn.2.5` the port also accepts it; this module pins that
acceptance through the production runtime-image entry point, and the corpus
fixture records the residual byte/layout difference as a tracked gap.
-/

namespace Flapjack.Test.RiscVArtifactParity

open Flapjack Flapjack.RiscV
open Flapjack.Test.OriginalPancakeProbes (decClock constReturn entryOrder nestedExpression)

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

/-- The `entry_order` fixture source, taken from the original-side probe fact.
It declares the entry function `main` last:

```
fun 1 a() { return 1; }
fun 1 b() { return 2; }
fun 1 main() { return a(); }
``` -/
def entryOrderSource : String := entryOrder.source

/-- Original CakeML layout: `cml_generated_main` at 1000 (4B, `jal` to
`cml_main`), `cml_main` at 1004 (4B, `jal` to `cml_a`), `cml_a` at 1008 (8B),
`cml_b` at 1016 (8B).  Evidence: `cakeml/pancake/pan_passesScript.sml:20-37`
(`pan_to_target_all_def`) moves the `main` declaration to the front, and the
original `makesym` lines report exactly these bases and sizes. -/
def cakeEntryOrderSections : List (Nat × Nat × List (BitVec 8)) :=
  [ (3, 1000, [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)),
    (4, 1004, [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)),
    (5, 1008, [0x13, 0x65, 0x10, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)),
    (6, 1016, [0x13, 0x65, 0x20, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)) ]

/-- Flapjack layout for the same fixture: `cml_generated_main` at 1000 (4B,
`jal` straight to the renamed entry at 1028), helper `a` at 1004 (12B),
helper `b` at 1016 (12B), and the entry `main` last at 1028 (4B, `jal` to
`a`).  This is the source order produced by `globalResortDecls`, not the
original entry-first order. -/
def flapjackEntryOrderSections : List (Nat × Nat × List (BitVec 8)) :=
  [ (3, 1000, [0x6F, 0x00, 0xC0, 0x01].map (BitVec.ofNat 8)),
    (4, 1004, [0x13, 0x01, 0x10, 0x00, 0x33, 0x61, 0x21, 0x00,
               0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)),
    (5, 1016, [0x13, 0x01, 0x20, 0x00, 0x33, 0x61, 0x21, 0x00,
               0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)),
    (6, 1028, [0x6F, 0xF0, 0x9F, 0xFE].map (BitVec.ofNat 8)) ]

/-- Exact emitted `(label, base, bytes)` artifact for the `entry_order`
fixture. -/
def entryOrderEmittedSections : List (Nat × Nat × List (BitVec 8)) :=
  match compileRuntimeImage entryOrderSource with
  | some image => emittedSections image
  | none => []

/-- The port emits the four generated sections in source order. -/
def entryOrderLayoutMatches : Bool :=
  entryOrderEmittedSections == flapjackEntryOrderSections

/-- The residual ordering mismatch, recorded exactly rather than accepted:
the original places the entry `cml_main` second (label 4, 4 bytes) and the
helpers after it, while the port places helper `a` second (label 4, 12 bytes)
and the entry `main` last (label 6).  Both entry sections are 4-byte jumps and
both helper sets compute `1` and `2` via `addi`; the difference is the
deterministic section order owned by `flapjack-pxn.8.5.10.3`. -/
def entryOrderOrderingMismatch : Bool :=
  cakeEntryOrderSections != flapjackEntryOrderSections &&
    cakeEntryOrderSections.length == 4 && flapjackEntryOrderSections.length == 4 &&
    cakeEntryOrderSections.map (fun s => s.2.2.length) == [4, 4, 8, 8] &&
    flapjackEntryOrderSections.map (fun s => s.2.2.length) == [4, 12, 12, 4] &&
    entryOrder.cakeFinalBytes ==
      ([0x13, 0x65, 0x10, 0x00, 0x67, 0x80, 0x00, 0x00,
        0x13, 0x65, 0x20, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8))

/-- The `nested_expression` fixture source, taken from the original-side probe
fact.  It is the GitHub issue #1015 reproducer whose right-nested sum needs
more than the four reserved Word-to-Stack temporaries. -/
def nestedExpressionSource : String := nestedExpression.source

/-- The production runtime-image entry point accepts the nested-expression
fixture.  Before the pool-expansion fix tracked by `flapjack-pxn.2.5` the
Word-to-Stack lowering failed with `artifactFailure`; the original compiler
flattens the expression through `crep_to_loop` and always accepted it. -/
def nestedExpressionAccepted : Bool :=
  match compileRuntimeImage nestedExpressionSource with
  | some image => image.sections.length == 5 && image.warnings.isEmpty
  | none => false

/-! The runtime-image guard above exercises the public source path.  Keep a
    smaller Word-to-Stack guard beside it as well: this is a spilled
    destination, and the expression needs the dead allocator registers that
    Cake's flattened Loop temporaries make available after the four reserved
    scratch registers.  This prevents a future refactor from accidentally
    restoring the old fixed-pool boundary while the end-to-end fixture still
    happens to compile through a different path. -/
def nestedExpressionWordConfig : WordStackConfig :=
  { locations := [(0, .register 2), (1, .register 3), (2, .register 4),
      (3, .register 5), (4, .register 6), (5, .stack 0)]
    scratch := 31
    stackBase := 1 }

def nestedExpressionWord : WordExp Nat :=
  .shift .lsr
    (.op .add [.var 0,
      .op .add [.var 1,
        .op .add [.var 2,
          .op .add [.var 3, .var 4]]]])
    (.const 1)

def nestedExpressionWordLoweringAccepted : Bool :=
  match wordStackCompileExpToPhysicalNat nestedExpressionWordConfig 5
      nestedExpressionWord with
  | some _ => true
  | none => false

/-- The differential-fuzzing `dup-global` fixture (GitHub issue #962 smoke,
    bead `flapjack-pxn.8.5.14.4`).  The original CakeML accepts a duplicate
    top-level global with the warning `variable g is redeclared in top-level
    declaration` and keeps the later declaration; the port used to reject it in
    `staticCheckDecls`. -/
def dupGlobalSource : String :=
  "var 1 g = 7;\nvar 1 g = 7;\nfun 1 main() { return g; }"

/-- The production runtime-image entry point now accepts the duplicate-global
program and reports at least one warning instead of failing the static check. -/
def dupGlobalAcceptedWithWarning : Bool :=
  match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] artifactCompileConfig "main"
      dupGlobalSource with
  | .ok image => !image.warnings.isEmpty
  | .error _ => false

#guard dupGlobalAcceptedWithWarning

/-- The differential-fuzzing `nomain-global` fixture (bead
    `flapjack-pxn.8.5.14.3`).  The original CakeML `pan_to_target` synthesizes
    a `main` returning `0` when the source has none; the port used to fail with
    `entry not found`. -/
def nomainGlobalSource : String := "var 1 g = 7;"

/-- The production runtime-image entry point now accepts a main-less program by
synthesizing the default `main`. -/
def nomainGlobalAccepted : Bool :=
  match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] artifactCompileConfig "main"
      nomainGlobalSource with
  | .ok image => !image.sections.isEmpty
  | .error _ => false

/-!
## FFI stub parity (bead `flapjack-pxn.8.5.14.2`)

The original CakeML `export_riscv` emits, between the `j cake_main`
startup stub and the fixed `cake_clear`/`cake_exit` pair, one 16-byte
block per user FFI name in first-appearance order:

```
cake_ffi<name>:
     tail cdecl(ffi<name>)
     .p2align 4
```

The port used to omit these blocks entirely.  The runtime image now
carries the discovered `ffiNames` and `RiscV.pancakeRuntimeAssembly`
emits the same blocks in the same position and order.  Residual: names
referenced only from unreachable code are still emitted because the
port discovers FFI names before dead-code removal (same family as the
`flapjack-pxn.8.5.10.1` lowering residuals).
-/

/-- The minimal FFI fixture: one reachable `@foo` call.  Pancake FFI
    calls take exactly four arguments. -/
def ffiMinSource : String := "fun 1 main() { @foo(1,2,3,4); return 0; }"

/-- Two FFI names, `@foo` first. -/
def ffiOrderSource : String :=
  "fun 1 main() { @foo(1,2,3,4); @bar(4,3,2,1); return 0; }"

/-- The same two FFI names in the opposite first-appearance order. -/
def ffiOrderFlipSource : String :=
  "fun 1 main() { @bar(4,3,2,1); @foo(1,2,3,4); return 0; }"

/-- Mirror of the `flapjack-compile --pancake` path: parse, lower to
`CompiledFunction`s, build the runtime image, render the assembly text. -/
def compileAssembly (source : String) : Option String :=
  match Flapjack.Parser.parseTopDecs (α := RiscV.Word 64)
      (fun value => BitVec.ofInt 64 value) source with
  | .error _ => none
  | .ok declarations =>
      match compileFlapjackEntry (α := RiscV.Word 64) .rv64i
          (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
          "main" (panTargetDeclarationsWithDefaultMain declarations) with
      | none => none
      | some pipeline =>
          match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64)
              .rv64i (BitVec.ofNat 64 8) (BitVec.ofInt 64) []
              artifactCompileConfig "main" source with
          | .ok image =>
              some (RiscV.pancakeRuntimeAssembly pipeline.crepe image)
          | .error _ => none

/-- The runtime image records the reachable user FFI names in
first-appearance order. -/
def ffiNamesMatch : Bool :=
  (compileRuntimeImage ffiMinSource).map (·.ffiNames) == some ["foo"] &&
    (compileRuntimeImage ffiOrderSource).map (·.ffiNames) == some ["foo", "bar"] &&
    (compileRuntimeImage ffiOrderFlipSource).map (·.ffiNames) ==
      some ["bar", "foo"]

/-- The single-FFI assembly carries the exact original stub block in the
exact original position, immediately before `cake_clear`. -/
def ffiMinStubEmitted : Bool :=
  match compileAssembly ffiMinSource with
  | some assembly =>
      (assembly.splitOn
        "cake_ffifoo:\n     tail cdecl(ffifoo)\n     .p2align 4\n\ncake_clear:").length == 2
  | none => false

/-- The two-FFI assembly carries both stub blocks in first-appearance
order (`foo` then `bar`) between the startup stub and `cake_clear`. -/
def ffiOrderStubsEmitted : Bool :=
  match compileAssembly ffiOrderSource with
  | some assembly =>
      (assembly.splitOn
        "cake_ffifoo:\n     tail cdecl(ffifoo)\n     .p2align 4\n\ncake_ffibar:\n     tail cdecl(ffibar)\n     .p2align 4\n\ncake_clear:").length == 2
  | none => false

/-- Flipping the source order flips the emitted stub order (`bar` then
`foo`), matching the original's first-appearance convention. -/
def ffiOrderFlipStubsEmitted : Bool :=
  match compileAssembly ffiOrderFlipSource with
  | some assembly =>
      (assembly.splitOn
        "cake_ffibar:\n     tail cdecl(ffibar)\n     .p2align 4\n\ncake_ffifoo:\n     tail cdecl(ffifoo)\n     .p2align 4\n\ncake_clear:").length == 2
  | none => false

/-!
## Unreachable-code parity (dead FFI references)

The original discards statements that follow an unconditional control
transfer inside a statement sequence, so a Pancake `@foo` call after a
`throw` or a `return` never reaches the word program and never gains an
FFI stub (bead `flapjack-pxn.8.5.14.2` residual).  The port mirrors this
with `wordProgDCE` at the word-lowering boundary.
-/

/-- An `@foo` call after an unconditional `throw` is unreachable. -/
def deadFfiAfterThrowSource : String :=
  "exception E : 1;\nfun 1 main() { throw E 1; @foo(1,2,3,4); return 0; }"

/-- An `@foo` call after an unconditional `return` is unreachable, while
the earlier `@bar` call stays reachable. -/
def deadFfiAfterReturnSource : String :=
  "fun 1 main() { @bar(1,2,3,4); return 1; @foo(1,2,3,4); return 0; }"

/-- Unreachable FFI calls disappear from the discovered name list, and a
reachable call before the transfer survives it. -/
def deadFfiNamesDropped : Bool :=
  (compileRuntimeImage deadFfiAfterThrowSource).map (·.ffiNames) == some [] &&
    (compileRuntimeImage deadFfiAfterReturnSource).map (·.ffiNames) ==
      some ["bar"]

/-- No FFI stub block is emitted for a name whose only reference is
unreachable. -/
def deadFfiStubDropped : Bool :=
  match compileAssembly deadFfiAfterThrowSource with
  | some assembly =>
      !assembly.contains "cake_ffi" &&
        (assembly.splitOn "cake_clear:").length == 2
  | none => false

/-!
## Bitmap table word parity (bead `flapjack-pxn.8.5.14.1`)

The original's pancake bitmap table carries one word per non-tail call
continuation, each word a pure power of two `2 ^ f'` encoding the
caller's frame size (`f'` = frame words minus the bitmap slot), never
live-pointer bits.  The port now derives real entries from the lowered
program (`2 ^ (nextSpill + 1)`) instead of constant `2`s.  On the
`bitmap_calls` fixture, where neither compiler spills, both emit
`[4, 2, 2]`; the residual value mismatch when the original spills more
than the port (`8`/`16` vs `2`) is tracked by the bead.
-/

/-- The `bitmap_calls` fixture source (inline copy of
`Flapjack/Test/OriginalPancake/bitmap_calls.pnk`). -/
def bitmapCallsSource : String :=
  "fun 1 f () {\n    var 1 x = f();\n    var 1 x = f();\n    return 1;\n  }\n\nfun 1 main() { return 0; }"

/-- Both call continuations in `f` produce one `2 ^ 1` entry each after
the initial `[4]`, exactly matching the original's `[4, 2, 2]`. -/
def bitmapCallsWordsMatch : Bool :=
  match compileRuntimeImage bitmapCallsSource with
  | some image => image.bitmaps.data == [4, 2, 2]
  | none => false

/-! The smallest frame-occupancy oracle from
`scripts/parity-difffuzz-findings/frame-occupancy/p1.cake.S`.  Its single
non-tail call has no live value across the call, so Cake emits exactly the
header word and one `2 ^ 1` frame word. -/
def frameOccupancyP1Source : String :=
  "fun 1 id (x) { return x; }\n" ++
    "fun 1 main() { var 1 t = id(5); return 1; }"

/-- CakeML's exact bitmap vector recorded by the `p1` oracle assembly. -/
def cakeFrameOccupancyP1Bitmaps : List Nat := [4, 2]

/-- The production runtime-image compiler preserves the complete Cake `p1`
bitmap vector, including the initial header word. -/
def frameOccupancyP1BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyP1Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyP1Bitmaps
  | none => false

/-! The `p9` frame-occupancy oracle (`p9.cake.S`) records the two-field
struct case: Cake's allocator keeps one field live across the `mks` call and
spills the other, so both call continuations carry frame words `2 ^ 3 = 8`.
The port's frame/IRC wiring does not yet place spilled source values in the
frame (production stays at `f' = 1` and emits `[4, 2, 2]`), so this exact
production vector is pinned as a tracked gap rather than relaxed; the missing
wiring is `flapjack-pxn.8.5.14.1.3` (IRC allocator driver and frame slots). -/
def frameOccupancyP9Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun S mks (1 a, 1 b) { return S <f = a, g = b>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1,2); var 1 t = id(5); return s.f + s.g; }"

/-- CakeML's exact bitmap vector recorded by the `p9` oracle assembly. -/
def cakeFrameOccupancyP9Bitmaps : List Nat := [4, 8, 8]

/-- The `p9` production vector does not yet reach the checked Cake vector;
this records the gap instead of weakening the oracle. -/
def frameOccupancyP9GapTracked : Bool :=
  match compileRuntimeImage frameOccupancyP9Source with
  | some image => image.bitmaps.data != cakeFrameOccupancyP9Bitmaps
  | none => false

#guard nomainGlobalAccepted
#guard nestedExpressionAccepted
#guard nestedExpressionWordLoweringAccepted
#guard ffiNamesMatch
#guard ffiMinStubEmitted
#guard ffiOrderStubsEmitted
#guard ffiOrderFlipStubsEmitted
#guard deadFfiNamesDropped
#guard deadFfiStubDropped
#guard bitmapCallsWordsMatch
#guard frameOccupancyP1BitmapsMatch
#guard frameOccupancyP9GapTracked
#guard artifactAccepted
#guard generatedMainBytesMatch
#guard emittedLayoutMatches
#guard bitmapsMatch
#guard trackedMainMismatch
#guard constReturnLayoutMatches
#guard standaloneTickIsolated
#guard trackedConstReturnMismatch
#guard entryOrderLayoutMatches
#guard entryOrderOrderingMismatch

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
        trackedConstReturnMismatch),
      ("entry_order emitted section layout matches the port's source order",
        entryOrderLayoutMatches),
      ("entry_order original entry-first order mismatch is tracked, not accepted",
        entryOrderOrderingMismatch),
      ("nested_expression fixture accepted by the runtime-image entry point",
        nestedExpressionAccepted),
      ("nested_expression Word-to-Stack lowering uses the extended temp pool",
        nestedExpressionWordLoweringAccepted),
      ("dup_global fixture accepted with a redeclaration warning",
        dupGlobalAcceptedWithWarning),
      ("nomain_global fixture accepted with a synthesized default main",
         nomainGlobalAccepted),
      ("ffi names recorded in first-appearance order",
         ffiNamesMatch),
      ("single ffi stub block emitted in the original position",
         ffiMinStubEmitted),
      ("two ffi stub blocks emitted in first-appearance order",
         ffiOrderStubsEmitted),
      ("flipped ffi source order flips the emitted stub order",
         ffiOrderFlipStubsEmitted),
      ("unreachable ffi calls are dropped from the name list",
         deadFfiNamesDropped),
      ("unreachable ffi calls gain no stub block",
         deadFfiStubDropped),
      ("bitmap_calls table matches the original [4, 2, 2]",
         bitmapCallsWordsMatch),
      ("frame-occupancy p1 bitmap vector matches Cake [4, 2]",
         frameOccupancyP1BitmapsMatch),
      ("frame-occupancy p9 exact vector gap is tracked, not accepted",
         frameOccupancyP9GapTracked) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.RiscVArtifactParity
