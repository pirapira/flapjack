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

`namedStructSource` declares a named struct and accesses its fields.  The
static checker used to leave the field list of a named shape empty, so any
`s.field` access was reported as an invalid named field even though the
reference compiler accepts it; `namedStruct*` pins the reference sections and
asserts the byte entry point accepts the fixture.

`sharedMemorySource` performs a shared-memory load (`!ld8`) from a computed
address expression.  The shared-memory lowering only accepted atomic addresses,
so a non-constant address such as `1000 + 12` failed even though the reference
compiler accepts it; `sharedMemory*` pins the reference sections and asserts the
byte entry point accepts the fixture.

`shadowingSource` redeclares a local (`var 1 x = 0; var 1 x = g();`) in one
body.  The reference compiler only logs a warning for the redeclaration, while
the static checker previously rejected the call-initialized declaration as a
scope error; `shadowing*` pins the reference sections and asserts the byte entry
point accepts the fixture.

`globalSharedLoadSource` loads into a word global (`!ldw g, 0`).  The static
checker previously searched only locals for the destination and rejected the
global, while `nonWordSharedLoadSource` loads into a tuple-shaped local, which
the reference compiler rejects.  Together the fixtures pin both directions of
the shared-memory load destination check.

`rotateSource` rotates a word right (`x #>> 1`) and adds it to the operand.
RISC-V has no rotate instruction, so the encoder expands `.ror` through the
reserved scratch register `31`; the word-to-stack pass used to leave the rotate
result in `31` whenever the destination happened to be the scratch register,
which the encoder then rejected.  `rotate*` pins the reference sections and
asserts the byte entry point accepts the fixture.

`largeShapeSource` declares a 33-word shape local, larger than the reserved
scratch range.  The identity word-to-stack path mapped every variable name
directly to a physical register, so the final return move failed once a value
landed in register `29` or `31`, and `registerOfNat` rejected names above `31`.
The checked byte entry point now uses the same allocator-aware full-SSA
pipeline as the image entry points, so `largeShape*` pins the reference sections
and asserts the byte entry point accepts the fixture.

`structStoreSource` stores a struct-valued local with `st`.  The original `st`
flattens its value and accepts any shape, but the static checker demanded a word
value and rejected this program.  The checker now only requires a word address,
and `structStore*` pins the reference sections and asserts acceptance.
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

/-- Named-struct program: the static field-list regression.  The reference
compiler accepted this while the static checker rejected every named field
access because a named shape carried no fields. -/
def namedStructSource : String :=
  "struct my_struct {\n  1 a,\n  1 b\n}\n" ++
    "fun 1 f(my_struct s) {\n  return s.a + s.b;\n}\n" ++
    "fun 1 main() { return f(my_struct <a = 3, b = 4>); }"

/-- Shared-memory load with a computed address: the nested-address shared
lowering regression.  The reference compiler accepts `!ld8 v, 1000 + 12` while
the shared-memory path previously required an atomic address. -/
def sharedMemorySource : String :=
  "fun 1 test() {\n  var v = 12;\n  !ld8 v, 1000 + 12;\n  return v;\n}\n" ++
    "fun 1 main() { return test(); }"

/-- Shadowed local declaration program: the redeclaration regression.  The
reference compiler accepts `var 1 x = 0; var 1 x = g();` in one body (it logs a
warning and keeps going), while the static checker previously rejected the
second declaration as a scope error. -/
def shadowingSource : String :=
  "var 1 x = 1;\n" ++
    "fun 1 g() { return 9; }\n" ++
    "fun 1 f() {\n  var 1 x = 0;\n  var 1 x = g();\n  return x;\n}\n" ++
    "fun 1 main() { return f(); }"

/-- Shared-memory load into a global word destination: the destination-lookup
regression.  The reference compiler accepts `!ldw g, 0` when `g` is a word
global, while the static checker previously only searched locals and reported
an unknown destination. -/
def globalSharedLoadSource : String :=
  "var 1 g = 1;\n" ++
    "fun 1 f () {\n  !ldw g, 0;\n  return 1;\n}\n" ++
    "fun 1 main() { return f(); }"

/-- Shared-memory load into a non-word local: the destination-shape regression.
The reference compiler rejects `!ldw x, 0` when `x` has a tuple/struct shape,
while the static checker previously accepted any local destination. -/
def nonWordSharedLoadSource : String :=
  "fun 1 f () {\n  var {1} x = <1>;\n  !ldw x, 0;\n  return 1;\n}\n" ++
    "fun 1 main() { return 0; }"

/-- Rotate-right program: the reserved-scratch regression.  The word-to-stack
pass used to leave the `.ror` result in the reserved scratch register `31`
instead of moving it out, which the RISC-V encoder rejects. -/
def rotateSource : String :=
  "fun 1 main() { var x = 5; return x + (x #>> 1); }"

/-- Large-shape local: a 33-word shape local occupies registers beyond the
reserved scratch range.  The identity Word-to-Stack path used to reject the
resulting move/encoding; the checked byte entry point now uses the
allocator-aware full-SSA pipeline, as the image entry points already did. -/
def largeShapeSource : String :=
  "fun 1 f () {\n  var 33 x = <" ++
    String.intercalate "," (List.replicate 33 "0") ++
    ">;\n  return 1;\n}\nfun 1 main() { return f(); }"

/-- Structured local store: the original `st` flattens its value, so a named
struct is stored word by word.  The static checker used to require a word
value and rejected this original-Pancake-accepted program. -/
def structStoreSource : String :=
  "struct s { 1 a, 1 b } fun 1 main() { var s x = s <a = 1, b = 2>; " ++
    "st 1000, x; return 0; }"

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

/-- CakeML `cml_generated_main` for `namedStructSource` (4 bytes). -/
def cakeNamedStructGeneratedMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_main` for `namedStructSource` (12 bytes). -/
def cakeNamedStructMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x65, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x65,
    BitVec.ofNat 8 0x30, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x6F,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40, BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_f` for `namedStructSource` (8 bytes). -/
def cakeNamedStructF : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x33, BitVec.ofNat 8 0x85, BitVec.ofNat 8 0xA5,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_generated_main` for `sharedMemorySource` (4 bytes). -/
def cakeSharedMemoryGeneratedMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_main` for `sharedMemorySource` (4 bytes). -/
def cakeSharedMemoryMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_test` for `sharedMemorySource` (12 bytes). -/
def cakeSharedMemoryTest : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x65, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x3F, BitVec.ofNat 8 0x03, BitVec.ofNat 8 0x45,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67,
    BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_generated_main` for `shadowingSource` (28 bytes). -/
def cakeShadowGeneratedMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x8C,
    BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x15,
    BitVec.ofNat 8 0x15, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0xA5, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x85,
    BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x65,
    BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0x30, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_main` for `shadowingSource` (4 bytes). -/
def cakeShadowMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0xC0,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_g` for `shadowingSource` (8 bytes). -/
def cakeShadowG : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x65, BitVec.ofNat 8 0x90,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_f` for `shadowingSource`; only its reference length is pinned. -/
def cakeShadowFLength : Nat := 144

/-- CakeML `cml_generated_main` for `globalSharedLoadSource` (28 bytes). -/
def cakeGlobalSharedLoadGeneratedMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x03, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x8C,
    BitVec.ofNat 8 0xFE, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x15,
    BitVec.ofNat 8 0x15, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0xA5, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x85,
    BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x65,
    BitVec.ofNat 8 0x10, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0x30, BitVec.ofNat 8 0xB5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_main` for `globalSharedLoadSource` (4 bytes). -/
def cakeGlobalSharedLoadMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_f` for `globalSharedLoadSource` (36 bytes). -/
def cakeGlobalSharedLoadFLength : Nat := 36

/-- CakeML `cml_generated_main` for `rotateSource` (4 bytes). -/
def cakeRotateGeneratedMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_main` for `rotateSource` (28 bytes). -/
def cakeRotateMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0xB7, BitVec.ofNat 8 0x0F, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x8F,
    BitVec.ofNat 8 0x7F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x37,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x05,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x15,
    BitVec.ofNat 8 0x05, BitVec.ofNat 8 0x02, BitVec.ofNat 8 0x33,
    BitVec.ofNat 8 0x65, BitVec.ofNat 8 0xF5, BitVec.ofNat 8 0x01,
    BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_generated_main` for `largeShapeSource` (4 bytes). -/
def cakeLargeShapeGeneratedMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_main` for `largeShapeSource` (4 bytes). -/
def cakeLargeShapeMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_f` for `largeShapeSource` (8 bytes). -/
def cakeLargeShapeFLength : Nat := 8

/-- CakeML `cml_generated_main` for `structStoreSource` (4 bytes). -/
def cakeStructStoreGeneratedMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x6F, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x40,
    BitVec.ofNat 8 0x00 ]

/-- CakeML `cml_main` for `structStoreSource` (32 bytes). -/
def cakeStructStoreMain : List (BitVec 8) :=
  [ BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x65, BitVec.ofNat 8 0x10,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x65,
    BitVec.ofNat 8 0x80, BitVec.ofNat 8 0x3E, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0xA5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x65, BitVec.ofNat 8 0x20,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x93, BitVec.ofNat 8 0x65,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x3F, BitVec.ofNat 8 0x23,
    BitVec.ofNat 8 0xB0, BitVec.ofNat 8 0xA5, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x13, BitVec.ofNat 8 0x65, BitVec.ofNat 8 0x00,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x67, BitVec.ofNat 8 0x80,
    BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00 ]

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

/-- The named-struct fixture must be accepted; the static checker previously
left named shapes with an empty field list and rejected every field access. -/
def namedStructBytesAccepted : Bool :=
  match compileSourceBytes namedStructSource with
  | some bytes => bytes.length > 0
  | none => false

/-- The shared-memory computed-address fixture must be accepted; the shared
lowering previously required an atomic address. -/
def sharedMemoryBytesAccepted : Bool :=
  match compileSourceBytes sharedMemorySource with
  | some bytes => bytes.length > 0
  | none => false

/-- The shadowed local declaration fixture must be accepted; the static checker
previously treated the second declaration in a body as a hard scope error. -/
def shadowingBytesAccepted : Bool :=
  match compileSourceBytes shadowingSource with
  | some bytes => bytes.length > 0
  | none => false

/-- The global shared-memory load destination fixture must be accepted; the
static checker previously looked only at locals. -/
def globalSharedLoadBytesAccepted : Bool :=
  match compileSourceBytes globalSharedLoadSource with
  | some bytes => bytes.length > 0
  | none => false

/-- The non-word shared-memory load destination fixture must be rejected; the
reference compiler rejects it and the static checker now matches. -/
def nonWordSharedLoadRejected : Bool :=
  (compileSourceBytes nonWordSharedLoadSource).isNone

/-- The rotate-right fixture must be accepted; the word-to-stack pass previously
left a `.ror` result in the reserved scratch register `31`. -/
def rotateBytesAccepted : Bool :=
  match compileSourceBytes rotateSource with
  | some bytes => bytes.length > 0
  | none => false

/-- The large-shape local fixture must be accepted; the identity source path
previously failed once a local needed register 29/31 or above. -/
def largeShapeBytesAccepted : Bool :=
  match compileSourceBytes largeShapeSource with
  | some bytes => bytes.length > 0
  | none => false

/-- The structured-store fixture must be accepted: the original `st` flattens
its value, so a struct-valued local is a legal store source. -/
def structStoreBytesAccepted : Bool :=
  match compileSourceBytes structStoreSource with
  | some bytes => bytes.length > 0
  | none => false

/-- The pinned CakeML reference sections keep their original byte lengths. -/
def cakeGoldenShape : Bool :=
  cakeGlobalGeneratedMain.length == 28 && cakeGlobalMain.length == 20 &&
    cakeMultiGeneratedMain.length == 40 && cakeMultiMain.length == 28 &&
    cakeNaryGeneratedMain.length == 52 && cakeNaryMain.length == 36 &&
    cakeMulGeneratedMain.length == 40 && cakeMulMain.length == 40 &&
    cakeNamedStructGeneratedMain.length == 4 && cakeNamedStructMain.length == 12 &&
    cakeNamedStructF.length == 8 &&
    cakeSharedMemoryGeneratedMain.length == 4 && cakeSharedMemoryMain.length == 4 &&
    cakeSharedMemoryTest.length == 12 &&
    cakeShadowGeneratedMain.length == 28 && cakeShadowMain.length == 4 &&
    cakeShadowG.length == 8 && cakeShadowFLength == 144 &&
    cakeGlobalSharedLoadGeneratedMain.length == 28 &&
    cakeGlobalSharedLoadMain.length == 4 && cakeGlobalSharedLoadFLength == 36 &&
    cakeRotateGeneratedMain.length == 4 && cakeRotateMain.length == 28 &&
    cakeLargeShapeGeneratedMain.length == 4 && cakeLargeShapeMain.length == 4 &&
    cakeLargeShapeFLength == 8 &&
    cakeStructStoreGeneratedMain.length == 4 && cakeStructStoreMain.length == 32

#guard globalBytesAccepted
#guard nestedGlobalBytesAccepted
#guard multiGlobalBytesAccepted
#guard naryGlobalBytesAccepted
#guard longMulGlobalBytesAccepted
#guard namedStructBytesAccepted
#guard sharedMemoryBytesAccepted
#guard shadowingBytesAccepted
#guard globalSharedLoadBytesAccepted
#guard nonWordSharedLoadRejected
#guard rotateBytesAccepted
#guard largeShapeBytesAccepted
#guard structStoreBytesAccepted
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
    checkBool "Pancake named-struct source compiles (bytes)"
      namedStructBytesAccepted,
    checkBool "Pancake shared-memory computed-address source compiles (bytes)"
      sharedMemoryBytesAccepted,
    checkBool "Pancake shadowed local declaration source compiles (bytes)"
      shadowingBytesAccepted,
    checkBool "Pancake global shared-memory load destination compiles (bytes)"
      globalSharedLoadBytesAccepted,
    checkBool "Pancake non-word shared-memory load destination rejected"
      nonWordSharedLoadRejected,
    checkBool "Pancake rotate-right source compiles (bytes)"
      rotateBytesAccepted,
    checkBool "Pancake large-shape local source compiles (bytes)"
      largeShapeBytesAccepted,
    checkBool "Pancake struct-valued local store source compiles (bytes)"
      structStoreBytesAccepted,
    checkBool "Pancake global source compiles (runtime image)"
      (runtimeImageAccepted globalSource),
    checkBool "Pancake global initializer changes artifact"
      initializerChangesArtifact,
    checkBool "CakeML global golden sections pinned" cakeGoldenShape
    ].mapM id
  pure (results.all id)

end Flapjack.Test.SourceGlobalParity
