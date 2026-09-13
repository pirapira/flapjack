# Pancake parity-testing workflow

Flapjack is a Lean port of the CakeML Pancake compiler. A regression test is
useful for porting only when it corresponds to behavior of the original
Pancake implementation. This applies to source-to-RISC-V tests and to tests
of intermediate computations, state transitions, and pass-local helpers.

## Evidence rule

Every porting test must compare the Lean result with one of these original
implementation boundaries:

1. the original CakeML Pancake executable, for source-level behavior and
   emitted artifacts; or
2. an HOL EVAL/probe of the exact original Pancake definition, for an
   intermediate function that is not observable through the executable.

A second Lean implementation, even if independently written, is not an
original-equivalence test and cannot close the corresponding Bead.

Each fixture records:

- the exact source file and definition name in `cakeml/pancake`;
- the input program or intermediate input;
- the original command or probe source used to obtain the expected result;
- the comparison boundary, including documented label/name normalization; and
- the checked-in expected output consumed by the Lean test.

## Adding an intermediate probe

Use the original HOL theory directly. The existing example is
[`scripts/hol-probes/loop_to_word_probeScript.sml`](../scripts/hol-probes/loop_to_word_probeScript.sml),
which evaluates definitions from
`cakeml/pancake/loop_to_wordScript.sml`. Its output is checked in beside the
probe and regenerated with:

```sh
scripts/hol-probes/regenerate.sh
```

The normal Lean build does not require HOL4: CI checks the checked-in fixture.
When changing the original reference or the probe, regenerate the output,
review the diff, and update the Lean test and its Bead with the source
reference and evidence.

## Adding a source-level parity test

Run both compilers on the same Pancake source:

```sh
cakeml/developers/bin/cake --pancake --target=riscv < program.pnk > program.cake.S
lake exe flapjack-compile program.pnk --assembly > program.flapjack.S
```

Use the shared scripts under `scripts/` for artifact parsing and documented
normalization. Store a stable, reviewable fixture when the test is intended to
run in `lake test`; do not make normal CI depend on a locally installed CakeML
binary.

## Adding an executable source probe

For a supported source fragment, add both sides of an execution observation:

1. add a small HOL probe under [`scripts/hol-probes`](../scripts/hol-probes)
   that evaluates the original `panSem` equation, and regenerate its checked-in
   `.out` file with `scripts/hol-probes/regenerate.sh`; and
2. add a Lean test under [`Flapjack/Test`](../Flapjack/Test) that parses the
   same source, lowers and links it, executes the linked RISC-V image with the
   bounded machine model, and compares its observable result with the probe
   result.

[`Flapjack/Test/EndToEndParity.lean`](../Flapjack/Test/EndToEndParity.lean)
contains independent original-semantics probes and linked-RISC-V execution
fixtures for return, addition, multiplication, conditionals, function calls,
and global initialization. They deliberately do not rely only on a Flapjack
correctness theorem: distinct compilers can satisfy the same source theorem
while emitting different code. Memory and FFI execution fixtures, plus exact
artifact parity for the source corpus, remain open follow-up work. These
fixtures are stable seeds for differential fuzzing against `cake`; a source
accepted by CakeML but not executable by Flapjack is a P1 compiler-parity bug.

For the external five-program artifact corpus, run
`scripts/parity-small-corpus.py`. It invokes both `cake` and
`flapjack-compile --assembly`, checks the pinned Cake output hashes, compares
runtime/entry/user sections without hiding byte differences, and succeeds only
when every residual difference has an owning bead. This artifact audit
complements the machine-execution fixture above; it does not replace it.

## Review and Beads

Keep the porting Bead open until the original evidence and the Lean test are
both present. Record the branch and commit in the Bead while work is in
progress. Agents share the combined PR, merge the coordinator's current head
before starting a new slice, and report every content commit so the combined
branch remains reproducible.

This workflow concerns implementation parity and regression evidence. The
validity and implications of theorems, including the not-yet-ported top-level
compiler-correctness theorem, are documented separately in
[`SOUNDNESS.md`](SOUNDNESS.md).
