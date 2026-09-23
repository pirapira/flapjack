# Flapjack

Flapjack is an in-progress Lean 4 port of the formally verified Pancake
compiler; the original HOL sources are in the [`cakeml/pancake`](cakeml/pancake)
submodule. It has an executable RV64I compiler path for a growing subset of
Pancake, but is not yet a complete replacement and does not yet prove
whole-compiler correctness. Only RISC-V is in scope; see
[`docs/SOUNDNESS.md`](docs/SOUNDNESS.md) for assurance limits and
[`docs/PARITY-TESTING.md`](docs/PARITY-TESTING.md) for reference comparisons.

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

For the parser API and its current limitations, see
[`Flapjack/Parser/README.md`](Flapjack/Parser/README.md).

When porting a definition or theorem, generate the local CakeML/HOL source
index with `python3 scripts/index-hol.py`. It records declaration locations,
theory dependencies, and the CakeML commit used; see
[`docs/HOL-INDEX.md`](docs/HOL-INDEX.md). The generated `.hol-index/` directory
is gitignored.
The evolving HOL-to-Lean source layout is recorded in
[`docs/HOL-LAYOUT.md`](docs/HOL-LAYOUT.md).

## Port in progress

Contributions are welcome. The RISC-V compiler port and its correctness proof
are still in progress. [GitHub issues](https://github.com/pirapira/flapjack/issues)
track work and claims; [`PLAN.md`](PLAN.md) gives the staged direction.
[`docs/SOUNDNESS.md`](docs/SOUNDNESS.md) describes assurance limits, external
assumptions, and out-of-scope gaps.
Start with the porting and verification rules in [`AGENTS.md`](AGENTS.md).
The bead and single-PR instructions in its *Fleet workflow* section apply to
the coordinated internal agents; outside contributors can open their own
focused PRs.

Work bottom-up from a desired theorem through its HOL dependencies: port small
definitions and supporting lemmas first. Use `@[hol ...]` tags and
`scripts/check-hol-refs.py --mapping` to locate existing work. Run
`python3 scripts/next-hol-port.py --file cakeml/pancake/FILE.sml` to list
untagged candidates in a script; `--goal HOL_NAME` limits the list to earlier
declarations, and `--kind Theorem` includes theorem candidates. Check the
source, Lean analogues, and issue claims before choosing a target: tags are
navigation aids, not evidence of equivalence or of a missing port.

If you use a coding agent, this is a suitable prompt for a small first PR:

```text
Find one unclaimed, narrowly scoped RISC-V Pancake porting issue. Follow its
HOL dependencies bottom-up; use scripts/next-hol-port.py and the existing
@[hol] tags to find one small definition that still needs a faithful Lean
port. If no issue is that small, propose a candidate before coding. Read
AGENTS.md and the corresponding HOL source. Port only that definition into
its counterpart Lean module, preserving its inputs, outputs, and edge cases.
Add a focused HOL EVAL probe and matching Lean tests for two representative
cases. Do not change the compiler pipeline or add a broad refactor. Run the
affected lake build, lake test, scripts/check-hol-refs.py, and
scripts/check-warnings.sh. Open one PR with the HOL reference, test results,
and any remaining gap in its description.
```
