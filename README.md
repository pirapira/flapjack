# Flapjack

Flapjack is beginning as a Lean 4 port of the formally verified Pancake
compiler. It is an early-stage project: the current Lean code covers the
front-end syntax and declaration-level checking foundations, the first Pancake-to-Crepe and
Crepe-to-Loop compiler slices, executable semantic fragments, and an initial
RISC-V model. The CakeML HOL development is included as the `cakeml`
submodule; its Pancake sources are in [`cakeml/pancake`](cakeml/pancake).

Pancake source text can be parsed into Flapjack AST values with
[`Flapjack/Parser.lean`](Flapjack/Parser.lean), a port of Pancake's own
`panLexer`, `panPEG` grammar and `panPtreeConversion` conversion.
`Flapjack.Parser.parseTopDecs (BitVec.ofInt 64) source` returns either a list
of declarations or a list of positioned errors. The module map, the divergences
from upstream, and the omissions are documented in
[`Flapjack/Parser/README.md`](Flapjack/Parser/README.md).

## Current status

The port has a working, checked RV64I source-entry path for a growing subset
of Pancake and selected pass-level and machine-level lemmas. It is not yet a
complete replacement for CakeML's Pancake compiler:
full runtime-image generation, broad source coverage, exact artifact parity,
general executable source corpus and differential execution coverage, and the
complete Pancake correctness theorem still require work. The current
claims and limitations are recorded explicitly in
[`docs/SOUNDNESS.md`](docs/SOUNDNESS.md).
The required workflow for tying internal and end-to-end tests to the original
Pancake implementation is in [`docs/PARITY-TESTING.md`](docs/PARITY-TESTING.md).

Backends other than RISC-V are out of scope for this port.

## Usage

Install the pinned Lean toolchain and build the library:

```sh
lake build
```

Run the executable regression suite, including the CakeML-derived RISC-V
byte goldens:

```sh
lake test
```

Compile a Pancake source file through the source-facing RV64I path:

```sh
lake exe flapjack-compile program.pnk > program.riscv.S
```

The compiler also reads source from standard input:

```sh
printf 'fun 1 main() { return 7; }\n' | lake exe flapjack-compile
```

The default output (also selected by `--assembly` or `--pancake`) follows the
original Pancake/CakeML RISC-V assembly artifact boundary: runtime data and
bitmap framing, `cml_main` startup, `cake_main`, linked code-section labels,
`.byte` payloads, and `cake_codebuffer_*` markers. It is not an ELF file. For
the historical raw byte artifact, use:

```sh
lake exe flapjack-compile --hex program.pnk > program.riscv.hex
```

The original reference compiler can be run locally with:

```sh
cakeml/developers/bin/cake --pancake --target=riscv < program.pnk > program.cake.S
```

Use the parity tests, [`docs/PARITY-TESTING.md`](docs/PARITY-TESTING.md), and
[`docs/SOUNDNESS.md`](docs/SOUNDNESS.md) when interpreting comparisons between
the two outputs. For randomized cross-checking, the deterministic
differential fuzzer `scripts/parity-difffuzz.py` compares full artifacts
(sections, bytes, frame, acceptance) against `cake` and files every unknown
mismatch as a bead; see the differential-fuzzing section of
[`docs/PARITY-TESTING.md`](docs/PARITY-TESTING.md).

When porting a definition or theorem, generate the local CakeML/HOL source
index with `python3 scripts/index-hol.py`. It records declaration locations,
theory dependencies, and the CakeML commit used; see
[`docs/HOL-INDEX.md`](docs/HOL-INDEX.md). The generated `.hol-index/` directory
is gitignored.

## Project map

The source-facing compiler follows the Pancake pass order through the modules
listed below. There is one shipped checked RISC-V path, implemented by
`Flapjack.CompileMain`; experimental alternative compiler entry points have
been removed so parity fixes cannot accidentally target a different pipeline.

- `Flapjack/Language.lean`, `Static.lean`, and `Semantics.lean`: Pancake AST,
  static checks, and source semantics.
- `Flapjack/PanSimp.lean`, `PanStructs.lean`, and `PanGlobals.lean`: the first
  source-to-source passes.
- `Flapjack/PanToCrep.lean`, `CrepeRuntime.lean`, `CrepToLoop.lean`, and
  `LoopEvaluate.lean`: Crep and Loop compilation and semantics.
- `Flapjack/LoopToWord.lean` and the `Flapjack/RiscV` modules: the Word,
  allocation, Stack, Lab, and RV64I portions used by the checked compiler.
- `Flapjack/Pipeline.lean` and `Flapjack/RiscV/PipelineDiagnostics.lean`: pass
  composition and explicit failure reporting.

The current tree intentionally does not contain a top-level Pancake compiler
correctness theorem. Existing proofs establish selected local properties only;
their validity and implications are described in
[`docs/SOUNDNESS.md`](docs/SOUNDNESS.md). The staged port is tracked in
[`PLAN.md`](PLAN.md).
