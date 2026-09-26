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
`addi a0,x0,7; ret`), so the original drops the standalone `Tick`.  Flapjack
now mirrors CakeML's `lab_filter`: the source/Word semantics retains Tick for
clock reasoning, while the final Lab artifact omits its no-op instruction.

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
Flapjack entry permutation and source-facing ABI mapping now produce the same
section order and helper bytes for this fixture.

The original-side facts are the `OriginalPancakeProbes.decClock` source-backed
probe, whose dependency is the direct HOL probe
`scripts/hol-probes/pan_sem_dec_clock_e2e_probeScript.sml`.  That probe
evaluates the original `panSem$evaluate` on `tick; return 7` and observes
`SOME (Return (ValWord 7w))` with the clock decremented from `5` to `4`, which
is the semantic result the generated artifact must implement.

The generated `cml_generated_main` and `cml_main` sections are byte-identical
for this fixture.  This is evidence for the source-facing ABI adapter and the
final Lab filtering pass; larger programs still have tracked allocator,
frame, FFI, and lowering gaps.

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
open Flapjack.Test.OriginalPancakeProbes
  (decClock constReturn entryOrder nestedExpression setVar emptyLocals)

/-- The checked source-facing pipeline configuration used by the compiler
entry point, kept local so this parity test does not import the executable
`CompileMain` module and collide with the test driver's `main`. -/
def artifactCompileConfig : StackRemoveConfig :=
  { storeBase := 10
    currHeap := 12
    scratch := 31
    addressScratch := 29
    stackPointer := 24
    bytesInWord := 8
    stackBase := 25
    wordShift := 3
    jump := false }

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

/-- Flapjack `cml_generated_main` bytes.  With the faithful `loop_to_word`
tail-call shape (`0 :: args`, loop_to_wordScript.sml:131) applied at the
same pipeline point Cake uses (inside `loop_to_word$comp`, not via a later
pan-to-word adapter), the dummy constant-`0` argument coalesces onto the
`x0` sink exactly as CakeML's does, so the port's artifact is just the
4-byte `jal`: byte-identical to Cake. -/
def flapjackGeneratedMainBytes : List (BitVec 8) :=
  [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)

/-- The wrapper is byte-identical to Cake: the former residual leading ABI
move for the dummy tail-call argument is gone now that the `0 :: args`
dummy is injected where Cake injects it. -/
def generatedMainExactMatch : Bool :=
  flapjackGeneratedMainBytes == cakeGeneratedMainBytes

/-- Flapjack `cml_main` bytes: Cake's 8-byte return shape.  The Lab filter
removes the no-op generated for Tick before final assembly. -/
def flapjackMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x70, 0x00,
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

/-- The runtime-image entry point accepts the fixture and exposes the two
source sections (the fixed Cake runtime is supplied separately by the
Pancake-compatible formatter) and no static warnings. -/
def artifactAccepted : Bool :=
  match compileRuntimeImage decClockSource with
  | some image => image.sections.length == 2 && image.warnings.isEmpty
  | none => false

/-- The generated initializer section is byte-identical to Cake (see
`flapjackGeneratedMainBytes`). -/
def generatedMainBytesMatch : Bool :=
  generatedMainExactMatch

/-- The port lays out the two emitted sections with `cml_generated_main` at
base 1000 (4 bytes: Cake's direct `jal`) and `cml_main` at base 1004,
exactly Cake's layout. -/
def emittedLayoutMatches : Bool :=
  decClockEmittedSections ==
    [ (3, 1000, flapjackGeneratedMainBytes),
      (4, 1004, flapjackMainBytes) ]

/-- The port's bitmap table for the fixture is the initial single word `[4]`. -/
def bitmapsMatch : Bool :=
  match compileRuntimeImage decClockSource with
  | some image => image.bitmaps.data == [4]
  | none => false

/-! The `dec_clock` artifact is now exact: Lab filtering removes the no-op
instruction while the source semantics still accounts for the tick. -/
def decClockExactParity : Bool :=
  cakeMainBytes == flapjackMainBytes

/-- The `const_return` fixture source: the no-tick counterpart to
`dec_clock`, taken from the original-side probe fact. -/
def constReturnSource : String := constReturn.source

/-- Flapjack `cml_main` bytes for the no-tick `return 7` fixture; this is now
byte-identical to Cake after the source-facing ABI adapter. -/
def flapjackConstReturnMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x70, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Exact emitted `(label, base, bytes)` artifact for the `const_return`
fixture. -/
def constReturnEmittedSections : List (Nat × Nat × List (BitVec 8)) :=
  match compileRuntimeImage constReturnSource with
  | some image => emittedSections image
  | none => []

/-- The port lays out the two emitted sections as it does for `dec_clock`:
`cml_generated_main` at base 1000 (4 bytes) and `cml_main` at base 1004,
exactly Cake's layout. -/
def constReturnLayoutMatches : Bool :=
  constReturnEmittedSections ==
    [ (3, 1000, flapjackGeneratedMainBytes),
      (4, 1004, flapjackConstReturnMainBytes) ]

/- The standalone tick is filtered at the final Lab boundary. -/
def standaloneTickFiltered : Bool :=
  flapjackMainBytes == flapjackConstReturnMainBytes

/-! The no-tick `const_return` artifact is exact. -/
def constReturnExactParity : Bool :=
  cakeMainBytes == flapjackConstReturnMainBytes

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

/-- Flapjack emits the same section order and bodies as CakeML for this
fixture.  With the `0 :: args` dummy injected at the Cake point in
`loop_to_word$comp` (see `flapjackGeneratedMainBytes`), the two entry
sections (`cml_generated_main` at label 3 and the tail-calling `cml_main`
at label 4) are Cake's 4-byte `jal` exactly, and the helper bodies
(labels 5 and 6) are byte-identical to Cake: the whole artifact now matches
`cakeEntryOrderSections`. -/
def flapjackEntryOrderSections : List (Nat × Nat × List (BitVec 8)) :=
  [ (3, 1000, [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)),
    (4, 1004, [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)),
    (5, 1008, [0x13, 0x65, 0x10, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)),
    (6, 1016, [0x13, 0x65, 0x20, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)),
    ]

/-- Exact emitted `(label, base, bytes)` artifact for the `entry_order`
fixture. -/
def entryOrderEmittedSections : List (Nat × Nat × List (BitVec 8)) :=
  match compileRuntimeImage entryOrderSource with
  | some image => emittedSections image
  | none => []

/-- The port now follows CakeML's entry-first section order. -/
def entryOrderLayoutMatches : Bool :=
  entryOrderEmittedSections == cakeEntryOrderSections

/-- The artifact is now byte-identical to Cake: the emitted sections equal
the port pin, and the port pin equals `cakeEntryOrderSections` (the former
residual leading dummy-argument ABI move in the two entry sections is
gone). -/
def entryOrderExactParity : Bool :=
  entryOrderEmittedSections == flapjackEntryOrderSections &&
    flapjackEntryOrderSections == cakeEntryOrderSections

def setVarMainExactParity : Bool :=
  match compileRuntimeImage setVar.source with
  | some image =>
      match emittedSections image with
      | _ :: (_, _, mainBytes) :: _ =>
          mainBytes ==
            [0x13, 0x65, 0xB0, 0x00, 0x67, 0x80, 0x00, 0x00].map
              (BitVec.ofNat 8)
      | _ => false
  | none => false

def emptyLocalsMainExactParity : Bool :=
  match compileRuntimeImage emptyLocals.source with
  | some image =>
      match emittedSections image with
      | _ :: (_, _, mainBytes) :: _ =>
          mainBytes ==
            [0x6F, 0x00, 0x40, 0x00].map
              (BitVec.ofNat 8)
      | _ => false
  | none => false

/-! ## CurrHeap materialisation parity (GH #1128)

Cake's word_inst inst_select_exp leaves a Lookup CurrHeap plus a
materialised constant as a register operation.  The Lab stage must not apply
an aliased-add peephole to that pair: it would emit a different immediate
instruction, or erase CurrHeap - 0 entirely. -/
def currHeapAddConstSource : String :=
  "fun 1 main() { return @base + 255; }"

def currHeapSubZeroSource : String :=
  "fun 1 main() { return @base - 0; }"

def currHeapAddConstExactParity : Bool :=
  match compileRuntimeImage currHeapAddConstSource with
  | some image =>
      match emittedSections image with
      | _ :: (_, _, mainBytes) :: _ =>
          mainBytes ==
            [0x13, 0x65, 0xF0, 0x0F, 0x33, 0x05, 0xA5, 0x01,
             0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)
      | _ => false
  | none => false

def currHeapSubZeroExactParity : Bool :=
  match compileRuntimeImage currHeapSubZeroSource with
  | some image =>
      match emittedSections image with
      | _ :: (_, _, mainBytes) :: _ =>
          mainBytes ==
            [0x13, 0x65, 0x00, 0x00, 0x33, 0x05, 0xA5, 0x01,
             0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)
      | _ => false
  | none => false

/-! ## Cake return-register oracle (`flapjack-pxn.8.5.10.1.1`)

The original Cake `callee_abi.pnk` artifact keeps the allocator-selected
Word return register through `word_to_stack` and `stack_to_lab`: its `main`
section ends in `jalr x0,a1,0` (`67 80 05 00`), rather than forcing the
architectural link register.  This source-facing guard consumes the same
production runtime-image path as `flapjack-compile --assembly` and pins that
oracle byte at the end of the emitted `main` section.
-/
def calleeAbiSource : String :=
  "fun 1 g(1 a, 1 b) { return a + b; }\n" ++
  "fun 1 main() { var 1 t = g(5, 7); var 1 u = t + 1; return u; }"

def calleeAbiMainReturnMatches : Bool :=
  match compileRuntimeImage calleeAbiSource with
  | some image =>
      match emittedSections image with
      | _ :: (_, _, mainBytes) :: _ =>
          mainBytes.drop (mainBytes.length - 4) ==
            [0x67, 0x80, 0x05, 0x00].map (BitVec.ofNat 8)
      | _ => false
  | none => false

/- The production allocator now preserves Cake's selected return register for
   this source witness.  Keep the original Cake terminal bytes as a checked
   regression oracle so a later ABI change cannot silently reintroduce the
   former gap. -/
#guard calleeAbiMainReturnMatches


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
  | some image => image.sections.length == 2 && image.warnings.isEmpty
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

/-! The explicit temporary-pool adapter remains covered independently of the
    source-facing selector boundary.  Keep a small structural oracle here so
    this does not silently become only a larger temporary-register pool: the
    innermost over-budget child (the four-add chain, budget three) is
    materialized into a fresh temporary, and the shift then combines that
    temporary with the constant inline. -/
def flattenExpressionProbe : WordProg Nat :=
  .assign 0 nestedExpressionWord

def flattenExpressionProbeMaterialized : WordProg Nat :=
  (RiscV.wordFlattenProgram 9 flattenExpressionProbe).program

def flattenExpressionProbeMatches : Bool :=
  match flattenExpressionProbeMaterialized with
  | .seq (.assign 9 (.op .add [.var 0,
        .op .add [.var 1,
          .op .add [.var 2,
            .op .add [.var 3, .var 4]]]]))
      (.assign 0 (.shift .lsr (.var 9) (.const 1))) => true
  | _ => false

/-! Materialization is bounded by the Word-to-Stack pool consumption, not by
    plain depth: a rotate node draws two pool entries (a destination register
    distinct from the scratch target plus the right subtree), so a rotate
    around a rotated operand needs four entries even though its depth is
    three.  Register-pressure-heavy sections such as `ripemd160_block` keep
    every allocator register live, leaving only the three reserved entries
    and rejecting the depth-bounded tree. -/
def rorChainBudgetProbe : WordExp Nat :=
  .shift .ror
    (.shift .ror (.op .add [.var 1, .var 2]) (.const 3))
    (.const 5)

def rorChainBudgetMatches : Bool :=
  RiscV.wordExpLoweringBudget rorChainBudgetProbe == 4

def flattenRorChainProbe : WordProg Nat :=
  .assign 0 rorChainBudgetProbe

/-! The inner rotate (budget two) is materialized because an outer `ror`
    needs two pool entries; the outer rotate then runs inline on atoms. -/
def flattenRorChainProbeMatches : Bool :=
  match (RiscV.wordFlattenProgram 5 flattenRorChainProbe).program with
  | .seq (.assign 5 (.shift .ror (.op .add [.var 1, .var 2]) (.const 3)))
      (.assign 0 (.shift .ror (.var 5) (.const 5))) => true
  | _ => false

/-! An operator application wider than two arguments draws one pool entry and
    recurses with the remainder for every argument; with atom arguments the
    whole application stays within the reserved pool. -/
def wideOpBudgetMatches : Bool :=
  RiscV.wordExpLoweringBudget (α := Nat)
      (.op .add [.var 1, .var 2, .var 3, .var 4]) == 1

/-! The Word-to-Stack `set` compiler accepts only atom values, so a compound
    value is materialized into a fresh temporary before the store.  Without
    this, a depth-bounded flattener keeps a two-operand sum compound and the
    store lowering fails. -/
def flattenSetProbe : WordProg Nat :=
  .set .currHeap (.op .add [.var 1, .var 2])

def flattenSetProbeMatches : Bool :=
  match (RiscV.wordFlattenProgram 5 flattenSetProbe).program with
  | .seq (.assign 5 (.op .add [.var 1, .var 2]))
      (.set .currHeap (.var 5)) => true
  | _ => false

/-! ## Saturated-register exact oracles (bead `flapjack-pxn.2.5`, GH #1015)

Cake never rejects a nested expression: `crep_to_loop` flattens it into fresh
temporaries that participate in allocation and spill to the frame when the
registers run out.  The worst case for the port is a function where every
allocatable register (x2--x26 hardware, here `2..26`) already holds a
variable and the fresh materialization temporaries are themselves spilled:
the Word-to-Stack expression pool then contains only the three reserved
scratch registers.  The flattener must therefore guarantee that every
emitted assignment value fits three pool entries; these probes pin both the
acceptance and the exact spilled lowering in that configuration. -/

/-- Every allocatable register holds a variable; destinations `0`, `5`, `9`
    are spilled to stack slots. -/
def nestedExpressionSaturatedConfig : WordStackConfig :=
  { locations := [(0, .stack 0), (1, .register 5), (2, .register 6),
      (3, .register 7), (4, .register 8), (5, .stack 2), (9, .stack 1)]
      ++ (List.range 22).map (fun i => (100 + i, .register (9 + i))) ++
      [(200, .register 2), (201, .register 3), (202, .register 4)]
    scratch := 31
    stackBase := 1 }

/-- The flattened GH #1015 tree lowers with a saturated register file. -/
def saturatedNestedExpressionLowers : Bool :=
  match RiscV.wordToStackProgNat nestedExpressionSaturatedConfig
      flattenExpressionProbeMaterialized with
  | some _ => true
  | none => false

/-- The flattened rotate chain lowers with a saturated register file. -/
def saturatedRorChainLowers : Bool :=
  match RiscV.wordToStackProgNat nestedExpressionSaturatedConfig
      ((RiscV.wordFlattenProgram 5 flattenRorChainProbe).program) with
  | some _ => true
  | none => false

/-- Exact spilled lowering of the flattened GH #1015 tree in the saturated
    configuration: the materialized four-add chain is evaluated into the
    reserved registers `27`/`28`/`29` (innermost first, exactly Cake's
    bottom-up order), stored to temporary slot `2`, reloaded into scratch
    `31`, shifted, and stored to the destination slot `1`. -/
def saturatedNestedExpressionExact : Bool :=
  match RiscV.wordToStackProgNat nestedExpressionSaturatedConfig
      flattenExpressionProbeMaterialized with
  | some (.seq
      (.seq
        (.seq
          (.seq
            (.seq (.arith .add 27 7 8)
              (.seq (.arith .or 28 6 6) (.arith .add 28 28 27)))
            (.seq (.arith .or 29 5 5) (.arith .add 29 29 28)))
          (.seq (.stackLoad 31 1) (.arith .add 31 31 29)))
        (.stackStore 31 2))
      (.seq (.stackLoad 31 2)
        (.seq (.const 29 1)
          (.seq (.shift .lsr 31 31 29) (.stackStore 31 1))))) => true
  | _ => false

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

/- The byte-oriented source entry point must apply the same target preparation;
   Cake accepts this non-empty main-less source through its synthesized main. -/
def nomainGlobalBytesAccepted : Bool :=
  match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] artifactCompileConfig "main"
      nomainGlobalSource with
  | .ok artifact => !artifact.bytes.isEmpty
  | .error _ => false

#guard nomainGlobalBytesAccepted

/- Cake's target pass does not synthesize a default main for an actually empty
   declaration list; comment-only input therefore remains rejected. -/
def emptySource : String := "// no Pancake declarations\n"

def emptySourceRejected : Bool :=
  match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] artifactCompileConfig "main"
      emptySource with
  | .ok _ => false
  | .error _ => true

#guard emptySourceRejected

/-!
## FFI stub parity (bead `flapjack-pxn.8.5.14.2`)

The original CakeML `export_riscv` emits, between the `j cake_main`
startup stub and the fixed `cake_clear`/`cake_exit` pair, one 16-byte
block per user FFI name.  `find_ffi_names` records names in tail-first
collector order and the exporter reverses that list, yielding source order
for a straight-line section:

```
cake_ffi<name>:
     tail cdecl(ffi<name>)
     .p2align 4
```

The port used to omit these blocks entirely.  The runtime image now carries
the Cake collector-order `ffiNames`; `RiscV.pancakeRuntimeAssembly` reverses
this list at the artifact boundary, just like Cake.
Residual: names
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
  match hparse : Flapjack.Parser.parseTopDecs (α := RiscV.Word 64)
      (fun value => BitVec.ofInt 64 value) source with
  | .error _ => none
  | .ok declarations =>
      let hparsed := Flapjack.Parser.parseTopDecs_declByteRanged
        (BitVec.ofInt 64) source false declarations hparse
      let htarget := panTargetDeclarationsWithDefaultMain_byteRanged
        declarations hparsed
      match compileFlapjackEntryCake .rv64i
          (BitVec.ofNat 64 8) (fun value => BitVec.ofNat 64 value)
          "main" (panTargetDeclarationsWithDefaultMain declarations)
          (some (.isTrue htarget)) with
      | none => none
      | some pipeline =>
          match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64)
              .rv64i (BitVec.ofNat 64 8) (BitVec.ofInt 64) []
              artifactCompileConfig "main" source with
          | .ok image =>
              some (RiscV.pancakeRuntimeAssembly pipeline.crepe image)
          | .error _ => none

/-- The runtime image records reachable user FFI names in Cake's tail-first
collector order. -/
def ffiNamesMatch : Bool :=
  (compileRuntimeImage ffiMinSource).map (·.ffiNames) == some ["foo"] &&
    (compileRuntimeImage ffiOrderSource).map (·.ffiNames) == some ["bar", "foo"] &&
    (compileRuntimeImage ffiOrderFlipSource).map (·.ffiNames) ==
      some ["foo", "bar"]

def ffiCollectorOrderGuard : Bool :=
  match RiscV.wordProgFfiNamesCake
      (.seq (.ffi "foo" 1 2 3 4 ([], []))
        (.ffi "bar" 1 2 3 4 ([], [])) : WordProg Nat) with
  | ["bar", "foo"] => true
  | _ => false

#guard ffiCollectorOrderGuard

/-- The single-FFI assembly carries the exact original stub block in the
exact original position, immediately before `cake_clear`. -/
def ffiMinStubEmitted : Bool :=
  match compileAssembly ffiMinSource with
  | some assembly =>
      (assembly.splitOn
        "cake_ffifoo:\n     tail cdecl(ffifoo)\n     .p2align 4\n\ncake_clear:").length == 2
  | none => false

/-- Cake exports the two-FFI blocks in source order (`foo` then `bar`) after
    reversing its tail-first collector list. -/
def ffiOrderStubsEmitted : Bool :=
  match compileAssembly ffiOrderSource with
  | some assembly =>
      (assembly.splitOn
        "cake_ffifoo:\n     tail cdecl(ffifoo)\n     .p2align 4\n\ncake_ffibar:\n     tail cdecl(ffibar)\n     .p2align 4\n\ncake_clear:").length == 2
  | none => false

/-- Flipping the source order flips the emitted stub order (`bar` then `foo`),
    matching Cake's exported artifact. -/
def ffiOrderFlipStubsEmitted : Bool :=
  match compileAssembly ffiOrderFlipSource with
  | some assembly =>
      (assembly.splitOn
        "cake_ffibar:\n     tail cdecl(ffibar)\n     .p2align 4\n\ncake_ffifoo:\n     tail cdecl(ffifoo)\n     .p2align 4\n\ncake_clear:").length == 2
  | none => false

def bytesContain (needle haystack : List (BitVec 8)) : Bool :=
  match needle, haystack with
  | [], _ => true
  | _, [] => false
  | _, _ :: rest =>
      (haystack.take needle.length == needle) || bytesContain needle rest

/-! The exact FFI bytes remain a source-to-RISC-V differential obligation
tracked by `flapjack-pxn.8.5.14.7` and the parity corpus.  Until the complete
Cake call-frame prologue is ported, this build-time guard checks only the
interim invariant that the call is a real `jal` and not an `ecall`; keeping the
strict byte comparison in the external oracle prevents this from hiding the
known gap. -/
def ffiMinCallStubStructural : Bool :=
  let jalOpcode := [(BitVec.ofNat 8 0x6f)]
  let ecall := [0x73, 0x00, 0x00, 0x00].map (BitVec.ofNat 8)
  match compileRuntimeImage ffiMinSource with
  | some image =>
      match image.sections.find? (fun sec => sec.label == 4) with
      | some sec => bytesContain jalOpcode sec.bytes &&
          !bytesContain ecall sec.bytes
      | none => false
  | none => false

def ffiMinFramePrefix : Bool :=
  match compileRuntimeImage ffiMinSource with
  | some image =>
      match image.sections.find? (fun sec => sec.label == 4) with
      | some sec =>
          sec.bytes.take 4 == [0x13, 0x0c, 0x0c, 0xff].map (BitVec.ofNat 8)
      | none => false
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

/-! Constant-condition branches are also removed by Cake's `const_fp`, before
    FFI service discovery.  This is a separate guard from sequence-tail DCE:
    the call is syntactically inside a branch, but the branch itself is
    unreachable because `3 < 1` is constant false. -/
def deadFfiAfterConstantFalseSource : String :=
  "fun 1 main() { if (3 < 1) { @foo(1,2,3,4); } else { return 0; } return 0; }"

def deadFfiConstantFalseDropped : Bool :=
  (compileRuntimeImage deadFfiAfterConstantFalseSource).map (·.ffiNames) == some [] &&
    match compileAssembly deadFfiAfterConstantFalseSource with
    | some assembly => !assembly.contains "cake_ffi"
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

/-! The `bc` oracle exercises two self-recursive non-tail calls.  Cake's
    recursive continuations use the trivial frame word, yielding `[4, 2, 2]`.
    This is distinct from the non-recursive `bitmap_calls` fixture. -/
def frameOccupancyBcSource : String :=
  "fun 1 f () {\n" ++
    "  var 1 x = f();\n" ++
    "  var 1 x = f();\n" ++
    "  return 1;\n" ++
    "}\n\n" ++
    "fun 1 main() { return 0; }"

def cakeFrameOccupancyBcBitmaps : List Nat := [4, 2, 2]

def frameOccupancyBcBitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyBcSource with
  | some image => image.bitmaps.data == cakeFrameOccupancyBcBitmaps
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

/-! The `p2` oracle is the scalar-live baseline: `x` remains live across the
    non-tail `id` call, so Cake emits one two-word continuation frame
    (`[4, 4]`). -/
def frameOccupancyP2Source : String :=
  "fun 1 id (x) { return x; }\n" ++
    "fun 1 main() { var 1 x = 5; var 1 t = id(5); return x; }"

def cakeFrameOccupancyP2Bitmaps : List Nat := [4, 4]

def frameOccupancyP2BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyP2Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyP2Bitmaps
  | none => false

/-! The `p3` oracle keeps a one-field struct value live across the same
    non-tail call.  Cake's checked artifact has the minimal continuation
    frame `[4, 4]`. -/
def frameOccupancyP3Source : String :=
  "struct S { 1 f }\n" ++
    "fun 1 id (x) { return x; }\n" ++
    "fun 1 main() { var S s = S <f = 1>; var 1 t = id(5); return s.f; }"

def cakeFrameOccupancyP3Bitmaps : List Nat := [4, 4]

def frameOccupancyP3BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyP3Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyP3Bitmaps
  | none => false

/-! The `p4` oracle is the one-field CSE case: the same field is read twice
    after the non-tail call, while Cake still emits the minimal `[4, 4]`
    continuation vector. -/
def frameOccupancyP4Source : String :=
  "struct S { 1 f }\n" ++
    "fun 1 id (x) { return x; }\n" ++
    "fun 1 main() { var S s = S <f = 1>; var 1 t = id(5); return s.f + s.f; }"

def cakeFrameOccupancyP4Bitmaps : List Nat := [4, 4]

def frameOccupancyP4BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyP4Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyP4Bitmaps
  | none => false

/-! The `p5` oracle keeps one field of a two-field struct live across the
    non-tail call.  Cake's checked artifact uses the minimal continuation
    vector `[4, 4]`. -/
def frameOccupancyP5Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun 1 id (x) { return x; }\n" ++
    "fun 1 main() { var S s = S <f = 1, g = 2>; var 1 t = id(5); return s.f; }"

def cakeFrameOccupancyP5Bitmaps : List Nat := [4, 4]

def frameOccupancyP5BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyP5Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyP5Bitmaps
  | none => false

/-! The `p7` oracle keeps the scalar result of `id3` live across a second
    non-tail call.  Cake emits two minimal continuation frames, `[4, 4, 4]`.
    This is the scalar counterpart to the multi-call struct cases. -/
def frameOccupancyP7Source : String :=
  "fun 1 id3 (x) { return x; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var 1 x = id3(3); var 1 t = id(5); return x; }"

def cakeFrameOccupancyP7Bitmaps : List Nat := [4, 4, 4]

def frameOccupancyP7BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyP7Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyP7Bitmaps
  | none => false

/-! The p8 oracle keeps two returned two-field structs live across a later
    call.  Cake reserves three 32-word continuation frames ([4, 32, 32, 32])
    for the retained fields; this is a distinct high-occupancy witness from
    p9, whose two continuations are only eight words. -/
def frameOccupancyP8Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun S mks (1 a, 1 b) { return S <f = a, g = b>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() {\n" ++
    "  var S s1 = mks(1, 2);\n" ++
    "  var S s2 = mks(3, 4);\n" ++
    "  var 1 t = id(5);\n" ++
    "  return s1.f + s1.g + s2.f + s2.g + t;\n" ++
    "}"

def cakeFrameOccupancyP8Bitmaps : List Nat := [4, 32, 32, 32]

def frameOccupancyP8BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyP8Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyP8Bitmaps
  | none => false

/-! The `bm_min2` oracle is the bitmap-min spill case: both fields of the
    returned struct are read after `id`, so Cake emits two eight-word
    continuation entries (`[4, 8, 8]`). -/
def frameOccupancyBmMin2Source : String :=
  "struct S { 1 f1, 1 f2 }\n" ++
    "fun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\n" ++
    "fun 1 id(1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1, 2); var 1 t = id(5); return s.f1 + s.f2 + t; }"

def cakeFrameOccupancyBmMin2Bitmaps : List Nat := [4, 8, 8]

def frameOccupancyBmMin2BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyBmMin2Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyBmMin2Bitmaps
  | none => false

/-! The `live1` oracle keeps one field of a two-field struct live across an
    `id` call.  Cake's checked artifact has two minimal continuation entries,
    `[4, 4, 4]`. -/
def frameOccupancyLive1Source : String :=
  "struct S { 1 f1, 1 f2 }\n" ++
    "fun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\n" ++
    "fun 1 id(1 a) { return a; }\n" ++
    "fun 1 main() { var S s1 = mks(1, 2); var 1 t = id(7); return s1.f1 + t; }"

def cakeFrameOccupancyLive1Bitmaps : List Nat := [4, 4, 4]

def frameOccupancyLive1BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyLive1Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyLive1Bitmaps
  | none => false

/-! The `p9` frame-occupancy oracle (`p9.cake.S`) records the two-field
struct case: Cake's allocator keeps one field live across the `mks` call and
spills the other, so both call continuations carry frame words `2 ^ 3 = 8`.
The loop-live optimisation and the Cake frame-size computation now place the
spilled source values in the frame, so the production vector matches the
oracle exactly (`flapjack-pxn.8.5.14.1.5.1`). -/
def frameOccupancyP9Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun S mks (1 a, 1 b) { return S <f = a, g = b>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1,2); var 1 t = id(5); return s.f + s.g; }"

/-- CakeML's exact bitmap vector recorded by the `p9` oracle assembly. -/
def cakeFrameOccupancyP9Bitmaps : List Nat := [4, 8, 8]

/-- The `p9` production runtime-image compiler preserves the complete Cake
bitmap vector, including the initial header word. -/
def frameOccupancyP9BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyP9Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyP9Bitmaps
  | none => false

/-! The `p11` frame-occupancy oracle is the CSE-shaped companion to `p9`:
    the two-field result is read twice at the same field, and Cake retains a
    two-word frame for both non-tail continuations (`[4, 4, 4]`). -/
def frameOccupancyP11Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun S mks (1 a, 1 b) { return S <f = a, g = b>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1,2); var 1 t = id(5); return s.f + s.f; }"

def cakeFrameOccupancyP11Bitmaps : List Nat := [4, 4, 4]

def frameOccupancyP11BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyP11Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyP11Bitmaps
  | none => false

/-! The `wide` frame-occupancy oracle keeps the first and last fields of a
    six-field struct live across the `id` call.  Cake's checked artifact uses
    two eight-word continuation entries (`[4, 8, 8]`). -/
def frameOccupancyWideSource : String :=
  "struct S { 1 a, 1 b, 1 c, 1 d, 1 e, 1 f }\n" ++
    "fun S mks(1 x) { return S <a=x,b=x,c=x,d=x,e=x,f=x>; }\n" ++
    "fun 1 id(1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1); var 1 t = id(2); return s.a + s.f + t; }"

def cakeFrameOccupancyWideBitmaps : List Nat := [4, 8, 8]

def frameOccupancyWideBitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyWideSource with
  | some image => image.bitmaps.data == cakeFrameOccupancyWideBitmaps
  | none => false

/-! The `p10` frame-occupancy oracle is the first three-field struct case.
Cake's two non-tail continuations both retain a four-word frame (`f' = 4`),
so the checked bitmap payload is `[4, 16, 16]`.  The source is copied from
`scripts/parity-difffuzz-findings/frame-occupancy/p10.pnk`; the expected
vector is the corresponding `p10.cake.S` `.quad` payload. -/
def frameOccupancyP10Source : String :=
  "struct S { 1 f, 1 g, 1 h }\n" ++
    "fun S mks3 (1 a, 1 b, 1 c) { return S <f = a, g = b, h = c>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks3(1,2,3); var 1 t = id(5); return s.f + s.g + s.h; }"

def cakeFrameOccupancyP10Bitmaps : List Nat := [4, 16, 16]

def frameOccupancyP10BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyP10Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyP10Bitmaps
  | none => false

/-! The `p6` oracle covers the two-field struct return with two non-tail
continuations.  Cake keeps a two-word frame for both continuations, yielding
`[4, 4, 4]`; the source is copied from the checked p6 fixture. -/
def frameOccupancyP6Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun S mks (1 a, 1 b) { return S <f = a, g = b>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1,2); var 1 t = id(5); return s.f; }"

def cakeFrameOccupancyP6Bitmaps : List Nat := [4, 4, 4]

def frameOccupancyP6BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyP6Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyP6Bitmaps
  | none => false

/-! The `live3` oracle exercises four non-tail continuations over three
struct-valued locals.  Cake retains a four-word frame for each continuation,
so its checked bitmap payload is `[4, 16, 16, 16, 16]`. -/
def frameOccupancyLive3Source : String :=
  "struct S { 1 f1, 1 f2 }\n" ++
    "fun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\n" ++
    "fun 1 id(1 a) { return a; }\n" ++
    "fun 1 main() {\n" ++
    "  var S s1 = mks(1, 2);\n" ++
    "  var S s2 = mks(3, 4);\n" ++
    "  var S s3 = mks(5, 6);\n" ++
    "  var 1 t = id(7);\n" ++
    "  return s1.f1 + s2.f2 + s3.f1 + t;\n" ++
    "}"

def cakeFrameOccupancyLive3Bitmaps : List Nat := [4, 16, 16, 16, 16]

def frameOccupancyLive3BitmapsMatch : Bool :=
  match compileRuntimeImage frameOccupancyLive3Source with
  | some image => image.bitmaps.data == cakeFrameOccupancyLive3Bitmaps
  | none => false

/-- Source for the GH #1027 relational-condition case: `if x < 10` over a
parameter. -/
def relationalConditionSource : String :=
  "fun 1 f(1 x) {\n  if x < 10 { return 1; }\n  return 0;\n}\n" ++
    "fun 1 main() {\n  return f(5);\n}\n"

/-- The exact original-CakeML bytes for the `f` section of
`relational_condition.pnk`: `addi a1, x0, 10; bge a0, a1, +12;
addi a0, x0, 1; ret; addi a0, x0, 0; ret` (24 bytes).  The comparison is a
direct control-flow branch on the negated condition with the then-branch as
the fall-through path: no boolean is materialized and there is no extra
unconditional jump. -/
def cakeRelationalConditionBytes : List (BitVec 8) :=
  [0x93, 0x65, 0xa0, 0x00,
   0x63, 0x56, 0xb5, 0x00,
   0x13, 0x65, 0x10, 0x00,
   0x67, 0x80, 0x00, 0x00,
   0x13, 0x65, 0x00, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- The port now emits the same direct-branch section as CakeML for the
relational-condition fixture.  The original bytes remain pinned here so this
is an exact source-to-RISC-V oracle check. -/
def relationalConditionExactParity : Bool :=
  match compileRuntimeImage relationalConditionSource with
  | some image =>
      match emittedSections image with
      | _ :: _ :: fSection :: _ => fSection.2.2 == cakeRelationalConditionBytes
      | _ => false
  | none => false

def f01451Source : String :=
  "  var p = @base;\n" ++
    "fun 1 main() {\n" ++
    "  var a = ld8 p; var b = ld8 (p+1); var c = ld8 (p+2);\n" ++
    "  var d = ld8 (p+3); var e = ld8 (p+4); var t1 = ld8 (p+5);\n" ++
    "  var h = 0;\n" ++
    "  h = ((t1 + (a + (b + (c + (d + e))))) << 1000) >>> 1;\n" ++
    "  return h;\n" ++
    "}"

def cakeF01451MainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x00, 0x00,
   0x13, 0x55, 0x15, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

def f01451ExactParity : Bool :=
  match compileRuntimeImage f01451Source with
  | some image =>
      match emittedSections image with
      | [(_, 1000, _), (_, 1028, main)] => main == cakeF01451MainBytes
      | _ => false
  | none => false

/-- Source of the constant-store-reuse fixture (GitHub issue #1127, bead
    `flapjack-1kj`): a local store with a constant value followed by an
    expression that reuses the same constant.  This is the minimized
    differential-fuzz finding `f00198-s6-i00198-mutate`. -/
def constStoreReuseSource : String :=
  "fun 1 main() {\n" ++
    "  st (0 + 0), 1;\n" ++
    "  return @base | 1;\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for the fixture.  Cake rematerialises the
    store's constant (`li a0,1`) before the `or`; the port used to reuse the
    live register and emit only one `li`, dropping an instruction Cake keeps.
    `word_cse` must emit the original `OpCurrHeap` source register
    (`cakeml/compiler/backend/word_cseScript.sml:587-594`). -/
def cakeConstStoreReuseMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x10, 0x00,
   0x93, 0x65, 0x00, 0x00,
   0x23, 0xB0, 0xA5, 0x00,
   0x13, 0x65, 0x10, 0x00,
   0x33, 0x65, 0xA5, 0x01,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

def constStoreReuseExactParity : Bool :=
  match compileRuntimeImage constStoreReuseSource with
  | some image =>
      match emittedSections image with
      | [(3, 1000, generated), (4, 1004, main)] =>
          generated == [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8) &&
            main == cakeConstStoreReuseMainBytes
      | _ => false
  | none => false

/-- Source of the CurrHeap add fixture (differential-fuzz finding
    `f00036-s65-i00036-mutate`): `@base` lowers to a `CurrHeap` lookup, so
    Cake's `inst_select_exp` takes its `is_Lookup_CurrHeap` branch and
    materialises the constant plus a register add
    (`cakeml/compiler/backend/word_instScript.sml:246-275`) instead of folding
    it into an `addi`. -/
def currheapAddConstSource : String :=
  "fun 1 main() {\n" ++
    "  return @base + 255;\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for `@base + 255`:
    `li a0,255; add a0,a0,s10; ret` (s10 is the CurrHeap base). -/
def cakeCurrheapAddConstMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0xF0, 0x0F,
   0x33, 0x05, 0xA5, 0x01,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

def currheapAddConstExactParity : Bool :=
  match compileRuntimeImage currheapAddConstSource with
  | some image =>
      match emittedSections image with
      | [(3, 1000, generated), (4, 1004, main)] =>
          generated == [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8) &&
            main == cakeCurrheapAddConstMainBytes
      | _ => false
  | none => false

/-- Source of the CurrHeap zero-sub fixture: `@base - 0` reaches the same
    materialised-constant register add, so Cake keeps `li a0,0; add a0,a0,s10`
    rather than eliding the computation. -/
def currheapSubZeroSource : String :=
  "fun 1 main() {\n" ++
    "  return @base - 0;\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for `@base - 0`:
    `li a0,0; add a0,a0,s10; ret`. -/
def cakeCurrheapSubZeroMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x00, 0x00,
   0x33, 0x05, 0xA5, 0x01,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

def currheapSubZeroExactParity : Bool :=
  match compileRuntimeImage currheapSubZeroSource with
  | some image =>
      match emittedSections image with
      | [(3, 1000, generated), (4, 1004, main)] =>
          generated == [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8) &&
            main == cakeCurrheapSubZeroMainBytes
      | _ => false
  | none => false

/-- Source of the CurrHeap-left / constant-right fixture:
    `(@base | 7) #>> 1`.  Cake's `inst_select_exp`
    (`cakeml/compiler/backend/word_instScript.sml:246-251`) tests
    `is_Lookup_CurrHeap e1 ∧ op ≠ Sub` before the `e2 = Const w` immediate
    fold, so the `| 7` keeps `Const temp 7; OpCurrHeap Or temp temp` instead
    of folding the constant into an `ori`. -/
def currheapConstLeftSource : String :=
  "fun 1 main() {\n" ++
    "  return (@base | 7) #>> 1;\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for `(@base | 7) #>> 1`:
    `ori a0,0,7; or a0,a0,s10; srli a0,a0,1; slli a0,a0,3;
     or a0,a0,s10; ret` (s10 is the CurrHeap base). -/
def cakeCurrheapConstLeftMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x70, 0x00,
   0x33, 0x65, 0xA5, 0x01,
   0x93, 0x5F, 0x15, 0x00,
   0x13, 0x15, 0xF5, 0x03,
   0x33, 0x65, 0xF5, 0x01,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

def currheapConstLeftExactParity : Bool :=
  match compileRuntimeImage currheapConstLeftSource with
  | some image =>
      match emittedSections image with
      | [(3, 1000, generated), (4, 1004, main)] =>
          generated == [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8) &&
            main == cakeCurrheapConstLeftMainBytes
      | _ => false
  | none => false

/-- Source of the `!ld8` CurrHeap-offset fixture (GitHub issue #1130, bead
    `flapjack-pxn.8.5.14.20`): a shared 8-bit load whose address is
    `@base + 8`.  Cake keeps CurrHeap (`@base`, lowered to a `CurrHeap`
    lookup) as the load base and selects the byte-offset load
    `word_instScript.sml` `MappedRead`/`Load8` encoding, i.e. the UNSIGNED
    `lbu` (funct3 4), not `lb`. -/
def ld8CurrheapOffsetSource : String :=
  "fun 1 main() {\n" ++
    "  var 1 y = 0;\n" ++
    "  !ld8 y, (@base + 8);\n" ++
    "  return y;\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for the fixture (base 1004, 12 bytes):
    `or a0,s10,s10; lbu a0,8(a0); ret`.  The port previously emitted
    `lb` (funct3 0) and could materialise the base into a temporary. -/
def cakeLd8CurrheapOffsetMainBytes : List (BitVec 8) :=
  [0x33, 0x65, 0xAD, 0x01,
   0x03, 0x45, 0x85, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

def ld8CurrheapOffsetExactParity : Bool :=
  match compileRuntimeImage ld8CurrheapOffsetSource with
  | some image =>
      match emittedSections image with
      | [(3, 1000, generated), (4, 1004, main)] =>
          generated == [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8) &&
            main == cakeLd8CurrheapOffsetMainBytes
      | _ => false
  | none => false

/-- Source of the CurrHeap large-offset load witness (GitHub issue #1132):
    `lds 1 (@base + 2048)`.  Cake only splits an `Op Add [exp'; Const w]`
    address when `addr_offset_ok c w` holds; 2048 is out of the 12-bit range,
    so Cake selects the whole address, reaching `Const temp 2048; OpCurrHeap
    Add tar temp` and keeping `s10` as the memory base. -/
def currheapLoadLargeOffsetSource : String :=
  "fun 1 main() {\n" ++
    "  return lds 1 (@base + 2048);\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for the fixture (base 1004, 20 bytes):
    `lui a0,0xFFFFF; xori a0,a0,-2048; add a0,a0,s10; ld a0,0(a0); ret`.
    The port previously materialised CurrHeap into a temporary, adding an
    `or a0,s10,s10` and a register add. -/
def cakeCurrheapLoadLargeOffsetMainBytes : List (BitVec 8) :=
  [0x37, 0xF5, 0xFF, 0xFF,
   0x13, 0x45, 0x05, 0x80,
   0x33, 0x05, 0xA5, 0x01,
   0x03, 0x35, 0x05, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

def currheapLoadLargeOffsetExactParity : Bool :=
  match compileRuntimeImage currheapLoadLargeOffsetSource with
  | some image =>
      match emittedSections image with
      | [(3, 1000, generated), (4, 1004, main)] =>
          generated == [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8) &&
            main == cakeCurrheapLoadLargeOffsetMainBytes
      | _ => false
  | none => false

/-- Source of the whole-artifact `hello.pnk` fixture (GitHub issue #1022 /
    bead `flapjack-8tb`). -/
def helloSource : String :=
  "// Smoke test: echo input length into the output region and halt.\n" ++
    "fun 1 main() {\n" ++
    "  var len = 0;\n" ++
    "  !ldw len, 1073741832;\n" ++
    "  var out = 2684420096;\n" ++
    "  var i = 0;\n" ++
    "  while i < 69 {\n" ++
    "    !st8 out + i, 0;\n" ++
    "    i = i + 1;\n" ++
    "  }\n" ++
    "  !st8 out + 32, 1;\n" ++
    "  !stw out + 40, len;\n" ++
    "  @halt(@base, 0, @base, 0);\n" ++
    "  return 0;\n" ++
    "}"

/-- Original CakeML `cml_main` length for `hello.pnk` from the checked
assembly oracle. -/
def cakeHelloMainLength : Nat := 152

/- Port-side layout pin for `hello.pnk`; with the same `jump := false`
configuration used by `flapjack-compile`, the source-facing runtime image has
Cake's 152-byte `cml_main` section. -/
def helloRuntimeImage : Option (SourceRiscVRuntimeImage 64) :=
  compileRuntimeImage helloSource

/- The source-string path emits the same section labels, bases, and lengths as
the checked Cake artifact: a 4-byte generated entry at 1000 and a 152-byte
`cml_main` at 1004. -/
def helloEmittedSectionsMatch : Bool :=
  match helloRuntimeImage with
  | some image =>
      match emittedSections image with
      | [(3, 1000, generated), (4, 1004, main)] =>
          generated.length == 4 && main.length == cakeHelloMainLength
      | _ => false
  | none => false

/- The reduced allocator-colour witness is an original-Cake oracle regression.
   Cake emits four stack words ([4,16]) and a 256-byte process_transaction
   section; passing fresh SSA metadata into Word-to-Stack used to emit only
   three stack words and 232 bytes.  The full byte comparison remains pinned
   by scripts/parity-small-corpus.py. -/
def allocatorColourSource : String :=
  "exception BlockErr : 1;\n" ++
    "fun {1,1} tx_chain_id(1 tx) {\n" ++
    "  return <0, 0>;\n" ++
    "}\n" ++
    "fun 1 process_transaction(1 tx, 1 index, 1 pubkey) {\n" ++
    "  var {1,1} cid = tx_chain_id(tx);\n" ++
    "  if cid.0 != 0 {\n" ++
    "    if cid.1 != 0 {\n" ++
    "      throw BlockErr 0;\n" ++
    "    }\n" ++
    "  }\n" ++
    "  var nal = 0;\n" ++
    "  var i = 0;\n" ++
    "  while i < nal {\n" ++
    "  }\n" ++
    "  if (lds 1 (tx + 0)) == 0 {\n" ++
    "  } else {\n" ++
    "  }\n" ++
    "  return 0;\n" ++
    "}\n"

def allocatorColourCompileConfig : StackRemoveConfig :=
  { artifactCompileConfig with jump := false }

def allocatorColourRuntimeImage : Option (SourceRiscVRuntimeImage 64) :=
  match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] allocatorColourCompileConfig
      "main" allocatorColourSource with
  | .ok image => some image
  | .error _ => none

def allocatorColourOracleShape : Bool :=
  match allocatorColourRuntimeImage with
  | some image =>
      image.bitmaps.data == [4, 16] &&
        (emittedSections image).any (fun entry => entry.2.2.length == 256)
  | none => false

/- Cake's `ShareInst Store (Op Add [base; Const offset])` reaches the final
   RISC-V emitter as one base+offset memory instruction.  Keep a direct Lab
   regression guard for the source-shaped lowering used by `hello`. -/
def sharedWordStoreOffsetPeephole : Bool :=
  match labFlatten false 4 0 [] []
      ((.seq (.seq (.const 31 40) (.arith .add 29 12 31))
        (.shMem .store 10 29)) : StackProg Nat) with
  | ⟨[.asm (.memOffset .store .add 10 12 40) [] 0], false, 0⟩ => true
  | _ => false

/- Cake's shared-memory `Addr base offset` is distinct from ordinary memory;
   the carrier reaches the matching architectural offset store directly. -/
def sharedMemOffsetCarrierEncoding : Bool :=
  match labCompilePlain (width := 64)
      (.shareMemOffset .store8 10 11 (BitVec.ofNat 64 32)) with
  | some [.storeByteOffset 10 11 (BitVec.ofNat 64 32)] => true
  | _ => false

#guard helloEmittedSectionsMatch
#guard nomainGlobalAccepted
#guard nestedExpressionAccepted
#guard nestedExpressionWordLoweringAccepted
#guard flattenExpressionProbeMatches
#guard ffiNamesMatch
#guard ffiMinStubEmitted
#guard ffiOrderStubsEmitted
#guard ffiOrderFlipStubsEmitted
#guard ffiMinCallStubStructural
#guard ffiMinFramePrefix
#guard deadFfiNamesDropped
#guard deadFfiStubDropped
#guard deadFfiConstantFalseDropped
#guard bitmapCallsWordsMatch
#guard frameOccupancyBcBitmapsMatch
#guard frameOccupancyP1BitmapsMatch
#guard frameOccupancyP2BitmapsMatch
#guard frameOccupancyP3BitmapsMatch
#guard frameOccupancyP4BitmapsMatch
#guard frameOccupancyP5BitmapsMatch
#guard frameOccupancyP7BitmapsMatch
#guard frameOccupancyBmMin2BitmapsMatch
#guard frameOccupancyLive1BitmapsMatch
#guard frameOccupancyP9BitmapsMatch
#guard frameOccupancyP11BitmapsMatch
#guard frameOccupancyWideBitmapsMatch
#guard frameOccupancyP10BitmapsMatch
#guard frameOccupancyP6BitmapsMatch
#guard frameOccupancyLive3BitmapsMatch
#guard relationalConditionExactParity
#guard f01451ExactParity
#guard constStoreReuseExactParity
#guard currheapAddConstExactParity
#guard currheapSubZeroExactParity
#guard currheapConstLeftExactParity
#guard ld8CurrheapOffsetExactParity
#guard currheapLoadLargeOffsetExactParity
#guard sharedWordStoreOffsetPeephole
#guard sharedMemOffsetCarrierEncoding
#guard artifactAccepted
#guard generatedMainBytesMatch
#guard emittedLayoutMatches
#guard bitmapsMatch
#guard decClockExactParity
#guard constReturnLayoutMatches
#guard standaloneTickFiltered
#guard constReturnExactParity
#guard entryOrderLayoutMatches
#guard entryOrderExactParity
#guard setVarMainExactParity
#guard emptyLocalsMainExactParity
#guard currHeapAddConstExactParity
#guard currHeapSubZeroExactParity
#guard rorChainBudgetMatches
#guard flattenRorChainProbeMatches
#guard wideOpBudgetMatches
#guard flattenSetProbeMatches
#guard saturatedNestedExpressionLowers
#guard saturatedRorChainLowers
#guard saturatedNestedExpressionExact
#guard allocatorColourOracleShape

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
      ("dec_clock cml_main is byte-identical to Cake",
        decClockExactParity),
      ("const_return emitted section layout matches the original bases",
        constReturnLayoutMatches),
      ("standalone tick is filtered at the final Lab boundary",
        standaloneTickFiltered),
      ("const_return cml_main is byte-identical to Cake",
        constReturnExactParity),
      ("entry_order emitted section layout matches Cake",
        entryOrderLayoutMatches),
      ("entry_order artifact is byte-identical to Cake",
        entryOrderExactParity),
      ("set_var main section is byte-identical to Cake",
        setVarMainExactParity),
      ("empty_locals direct-call main is byte-identical to Cake",
        emptyLocalsMainExactParity),
      ("CurrHeap + materialised constant is byte-identical to Cake (GH #1128)",
        currHeapAddConstExactParity),
      ("CurrHeap - zero preserves Cake's register subtraction (GH #1128)",
        currHeapSubZeroExactParity),
      ("nested_expression fixture accepted by the runtime-image entry point",
        nestedExpressionAccepted),
      ("nested_expression Word-to-Stack lowering uses the extended temp pool",
        nestedExpressionWordLoweringAccepted),
      ("dup_global fixture accepted with a redeclaration warning",
        dupGlobalAcceptedWithWarning),
      ("nomain_global fixture accepted with a synthesized default main",
         nomainGlobalAccepted),
      ("nomain_global byte entry accepts the synthesized default main",
         nomainGlobalBytesAccepted),
      ("empty Pancake source is rejected like Cake",
         emptySourceRejected),
      ("ffi names recorded in Cake collector order",
         ffiNamesMatch),
      ("single ffi stub block emitted in the original position",
         ffiMinStubEmitted),
      ("two ffi stub blocks emitted in Cake order",
         ffiOrderStubsEmitted),
      ("flipped ffi source order flips the emitted stub order",
         ffiOrderFlipStubsEmitted),
      ("single ffi call lowers to the exact runtime-stub jump without ecall",
         ffiMinCallStubStructural),
      ("unreachable ffi calls are dropped from the name list",
         deadFfiNamesDropped),
      ("unreachable ffi calls gain no stub block",
         deadFfiStubDropped),
      ("bitmap_calls table matches the original [4, 2, 2]",
         bitmapCallsWordsMatch),
      ("frame-occupancy bc exact vector matches the Cake oracle",
         frameOccupancyBcBitmapsMatch),
      ("frame-occupancy p1 bitmap vector matches Cake [4, 2]",
         frameOccupancyP1BitmapsMatch),
      ("frame-occupancy p2 exact vector matches the Cake oracle",
         frameOccupancyP2BitmapsMatch),
      ("frame-occupancy p3 exact vector matches the Cake oracle",
         frameOccupancyP3BitmapsMatch),
      ("frame-occupancy p4 exact vector matches the Cake oracle",
         frameOccupancyP4BitmapsMatch),
      ("frame-occupancy p5 exact vector matches the Cake oracle",
         frameOccupancyP5BitmapsMatch),
      ("frame-occupancy p7 exact vector matches the Cake oracle",
         frameOccupancyP7BitmapsMatch),
      ("frame-occupancy p8 exact vector matches the Cake oracle",
         frameOccupancyP8BitmapsMatch),
      ("frame-occupancy bm_min2 exact vector matches the Cake oracle",
         frameOccupancyBmMin2BitmapsMatch),
      ("frame-occupancy live1 exact vector matches the Cake oracle",
         frameOccupancyLive1BitmapsMatch),
      ("frame-occupancy p9 exact vector matches the Cake oracle",
         frameOccupancyP9BitmapsMatch),
      ("frame-occupancy p11 exact vector matches the Cake oracle",
         frameOccupancyP11BitmapsMatch),
      ("frame-occupancy wide exact vector matches the Cake oracle",
         frameOccupancyWideBitmapsMatch),
      ("frame-occupancy p10 exact vector matches the Cake oracle",
         frameOccupancyP10BitmapsMatch),
      ("frame-occupancy p6 exact vector matches the Cake oracle",
         frameOccupancyP6BitmapsMatch),
      ("frame-occupancy live3 exact vector matches the Cake oracle",
         frameOccupancyLive3BitmapsMatch),
      ("relational condition direct-branch section is byte-identical to Cake",
        relationalConditionExactParity),
      ("f01451 out-of-range shift section is byte-identical to Cake",
        f01451ExactParity),
      ("constant-store reuse keeps Cake's rematerialised `li` (GH #1127)",
        constStoreReuseExactParity),
      ("CurrHeap add keeps Cake's materialised constant and register add",
        currheapAddConstExactParity),
      ("CurrHeap zero sub keeps Cake's materialised constant and register add",
        currheapSubZeroExactParity),
      ("CurrHeap-left constant keeps Cake's materialised constant and register add",
        currheapConstLeftExactParity),
      ("ld8 CurrHeap-offset load keeps Cake's base and lbu funct3 (GH #1130)",
        ld8CurrheapOffsetExactParity),
      ("out-of-range CurrHeap load offset keeps Cake's base register (GH #1132)",
        currheapLoadLargeOffsetExactParity) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.RiscVArtifactParity
