import Flapjack.Test.PipelineDiagnostics

/-!
# Original-Pancake global source parity fixtures

These fixtures were produced with the original CakeML Pancake reference
compiler for the minimal global program

```
var 1 g = 7;
fun 1 main() { return g; }
```

using

```
cake --pancake --target=riscv
```

Cake emits a fixed runtime followed by a generated initializer section
(`cml_generated_main`, 28 bytes) that stores the tagged constant `7` into the
global, and an entry body (`cml_main`, 20 bytes) that reloads it before
returning.  Flapjack currently lays out its own runtime and sections, so the
golden bytes here record the reference shape while the executable checks pin
the source-facing obligations: the checked byte pipeline and the runtime-image
pipeline must both accept the fixture, and the emitted artifact must include
the global initializer.

The byte-pipeline acceptance test is the regression for the nested-store
lowering failure fixed by "Lower nested global word expressions"; before that
change the entry points below rejected every program with a global.

The two-global binary-operator fixture `var 1 a = 1; var 1 b = 2;
fun 1 main() { return a + b; }` is the regression for the recursive
expression-lowering failure where a global load appeared as the right operand
of a binary node: the old lowering reserved two temporaries per binary node,
which exhausted the four reserved registers once both operands were nested
global addresses.  The `multiGlobal*` and `cakeMulti*` definitions pin the
reference sections and assert the byte and runtime-image entry points accept
it.

Two further fixtures cover arithmetic shapes the reference compiler accepts.
`naryGlobalSource` folds `a + b + c` into one flat associative `Add` node, which
the arity-2 expression lowering used to reject.  `longMulGlobalSource` uses
`a * b`, which the compiler lowers to `LongMul d d l r` with the high and low
product aliased onto one destination; the special-location contract used to
reject the alias even though only the low word is observed.  Both `naryGlobal*`
and `longMulGlobal*` definitions pin the reference sections and assert the byte
entry point accepts them.
-/

namespace Flapjack.Test.SourceGlobalParity

open Flapjack Flapjack.RiscV

/-- Source program used to generate the reference Pancake output. -/
def globalSource : String :=
  "var 1 g = 7;\nfun 1 main() { return g; }"

/-- Structured-shape variant accepted by the original Pancake parser. -/
def nestedGlobalSource : String :=
  "var {1} g = <7>;\nfun 1 main() { return g.0; }"

/-- Two-global binary-operator program: the recursive-lowering regression. -/
def multiGlobalSource : String :=
  "var 1 a = 1; var 1 b = 2; fun 1 main() { return a + b; }"

/-- Three-global associative-addition program: the n-ary Word arithmetic
regression.  The original Pancake parser folds `a + b + c` into one flat
`Add` node over three operands. -/
def naryGlobalSource : String :=
  "var 1 a = 1; var 1 b = 2; var 1 c = 3; fun 1 main() { return a + b + c; }"

/-- Two-global multiplication program: the low-word `LongMul` alias
regression.  The compiler emits `LongMul d d l r`, writing the high word and
then the low word to the same destination. -/
def longMulGlobalSource : String :=
  "var 1 a = 3; var 1 b = 4; fun 1 main() { return a * b; }"

/-- Global-free baseline used to show the initializer reaches the artifact. -/
def plainSource : String := "fun 1 main() { return 7; }"

/-- CakeML `cml_generated_main` for `globalSource` (offset 1000, 28 bytes). -/
def cakeGlobalGeneratedMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb5, BitVec.ofNat 8 0x8c,
    BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x15,
    BitVec.ofNat 8 0x15, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0xa5, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x85,
    BitVec.ofNat 8 0xff, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x65,
    BitVec.ofNat 8 0x70, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0x30, BitVec.ofNat 8 0xb5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6f, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_main` for `globalSource` (offset 1028, 20 bytes). -/
def cakeGlobalMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xb5, BitVec.ofNat 8 0x8c,
    BitVec.ofNat 8 0xfe, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x15,
    BitVec.ofNat 8 0x15, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0xa5, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x35, BitVec.ofNat 8 0x85,
    BitVec.ofNat 8 0xff, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_generated_main` for `multiGlobalSource` (40 bytes). -/
def cakeMultiGeneratedMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x8C,
    BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x15,
    BitVec.ofNat 8 0x15, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0xA5, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x85,
    BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x66,
    BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0xC5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x05,
    BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x65,
    BitVec.ofNat 8 0x20, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0x30, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_main` for `multiGlobalSource` (28 bytes). -/
def cakeMultiMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x8C,
    BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x15,
    BitVec.ofNat 8 0x15, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0xA5, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x35, BitVec.ofNat 8 0x05,
    BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x35,
    BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xA5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_generated_main` for `naryGlobalSource` (52 bytes). -/
def cakeNaryGeneratedMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x8C,
    BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x15,
    BitVec.ofNat 8 0x15, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0xA5, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x85,
    BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x66,
    BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0xC5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x05,
    BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x66,
    BitVec.ofNat 8 0x20, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0xC5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x85,
    BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x65,
    BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0x30, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_main` for `naryGlobalSource` (36 bytes). -/
def cakeNaryMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x8C,
    BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x15,
    BitVec.ofNat 8 0x15, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0xA5, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x35, BitVec.ofNat 8 0x85,
    BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x36,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0xB3,
    BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xC5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x35, BitVec.ofNat 8 0x85,
    BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x85,
    BitVec.ofNat 8 0xA5, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67,
    BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_generated_main` for `longMulGlobalSource` (40 bytes). -/
def cakeMulGeneratedMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x8C,
    BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x15,
    BitVec.ofNat 8 0x15, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0xA5, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x85,
    BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x66,
    BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0xC5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x05,
    BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x65,
    BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0x30, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_main` for `longMulGlobalSource` (40 bytes). -/
def cakeMulMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xE6, BitVec.ofNat 8 0x10,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0xB0,
    BitVec.ofNat 8 0x8C, BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x93,
    BitVec.ofNat 8 0x90, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xA0,
    BitVec.ofNat 8 0x01, BitVec.ofNat 8 0x83, BitVec.ofNat 8 0x30,
    BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x83,
    BitVec.ofNat 8 0x35, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0xFF,
    BitVec.ofNat 8 0x33, BitVec.ofNat 8 0xB6, BitVec.ofNat 8 0xB0,
    BitVec.ofNat 8 0x02, BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0xE5, BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x06,
    BitVec.ofNat 8 0x00 ]

/-- Run a source program through the checked RV64I byte entry point. -/
def compileSourceBytes (source : String) : Option (List (BitVec 8)) :=
  match compileFlapjackRiscVSourceBytesChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" source with
  | .ok artifact => some artifact.bytes
  | .error _ => none

/-- Run a source program through the checked runtime-image entry point. -/
def runtimeImageAccepted (source : String) : Bool :=
  match compileFlapjackRiscVSourceRuntimeImageChecked (width := 64) .rv64i
      (BitVec.ofNat 64 8) (BitVec.ofInt 64) [] checkedPipelineRemoveConfig
      "main" source with
  | .ok image => image.sections.length > 0 && image.bitmaps.data.length > 0
  | .error _ => false

/-- The global fixture must be accepted by the byte entry point. -/
def globalBytesAccepted : Bool :=
  match compileSourceBytes globalSource with
  | some bytes => bytes.length > 0
  | none => false

/-- The structured-shape global variant must also be accepted. -/
def nestedGlobalBytesAccepted : Bool :=
  match compileSourceBytes nestedGlobalSource with
  | some bytes => bytes.length > 0
  | none => false

/-- The global initializer must reach the artifact, making it longer than the
global-free baseline. -/
def initializerChangesArtifact : Bool :=
  match compileSourceBytes globalSource, compileSourceBytes plainSource with
  | some global, some plain => global.length > plain.length
  | _, _ => false

/-- The two-global binary-operator fixture must be accepted by the byte entry
point; this is the regression for the recursive expression-lowering failure. -/
def multiGlobalBytesAccepted : Bool :=
  match compileSourceBytes multiGlobalSource with
  | some bytes => bytes.length > 0
  | none => false

/-- The three-global n-ary addition fixture must be accepted; the flat `Add`
node previously fell through the arity-2 match and failed lowering. -/
def naryGlobalBytesAccepted : Bool :=
  match compileSourceBytes naryGlobalSource with
  | some bytes => bytes.length > 0
  | none => false

/-- The multiplication fixture must be accepted; the low-word `LongMul` alias
previously failed the special-location contract. -/
def longMulGlobalBytesAccepted : Bool :=
  match compileSourceBytes longMulGlobalSource with
  | some bytes => bytes.length > 0
  | none => false

/-- The pinned CakeML reference sections keep their original byte lengths. -/
def cakeGoldenShape : Bool :=
  cakeGlobalGeneratedMain.length == 28 && cakeGlobalMain.length == 20 &&
    cakeMultiGeneratedMain.length == 40 && cakeMultiMain.length == 28 &&
    cakeNaryGeneratedMain.length == 52 && cakeNaryMain.length == 36 &&
    cakeMulGeneratedMain.length == 40 && cakeMulMain.length == 40

#guard globalBytesAccepted
#guard nestedGlobalBytesAccepted
#guard multiGlobalBytesAccepted
#guard naryGlobalBytesAccepted
#guard longMulGlobalBytesAccepted
#guard initializerChangesArtifact
#guard cakeGoldenShape

def checkBool (name : String) (condition : Bool) : IO Bool := do
  if condition then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}"
    pure false

/-- Executable checks invoked from the `lake test` driver. -/
def runChecks : IO Bool := do
  let results ← [
    checkBool "Pancake global source compiles (bytes)" globalBytesAccepted,
    checkBool "Pancake structured global source compiles (bytes)"
      nestedGlobalBytesAccepted,
    checkBool "Pancake two-global source compiles (bytes)"
      multiGlobalBytesAccepted,
    checkBool "Pancake three-global n-ary source compiles (bytes)"
      naryGlobalBytesAccepted,
    checkBool "Pancake multiplication source compiles (bytes)"
      longMulGlobalBytesAccepted,
    checkBool "Pancake global source compiles (runtime image)"
      (runtimeImageAccepted globalSource),
    checkBool "Pancake global initializer changes artifact"
      initializerChangesArtifact,
    checkBool "CakeML global golden sections pinned" cakeGoldenShape
    ].mapM id
  pure (results.all id)

end Flapjack.Test.SourceGlobalParity
