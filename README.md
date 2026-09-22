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
The evolving HOL-to-Lean source layout is recorded in
[`docs/HOL-LAYOUT.md`](docs/HOL-LAYOUT.md).

## Port in progress

Contributions are welcome. The RISC-V compiler port and its correctness proof
are still in progress; see [`PLAN.md`](PLAN.md) for the staged work and
[`docs/SOUNDNESS.md`](docs/SOUNDNESS.md) for the current proof boundaries.
Start with the porting and verification rules in [`AGENTS.md`](AGENTS.md).
The bead and single-PR instructions in its *Fleet workflow* section apply to
the coordinated internal agents; outside contributors can open their own
focused PRs. Backends other than RISC-V are out of scope.

If you use a coding agent, this is a suitable prompt for a small first PR:

```text
Find one unclaimed, narrowly scoped Pancake-to-Lean porting issue on the
RISC-V path. Choose a single HOL definition that has no faithful Lean port;
if no issue is that small, propose one before coding. Read AGENTS.md and the
corresponding HOL source. Port only that definition into its counterpart Lean
module, preserving its inputs, outputs, and edge cases. Add a focused HOL EVAL
probe and matching Lean tests for two representative cases. Do not change the
compiler pipeline, add a broad refactor, or claim a theorem is ported. Run the
affected lake build, lake test, scripts/check-hol-refs.py, and
scripts/check-warnings.sh. Open one PR with the HOL reference, test results,
and any remaining gap in its description.
```
