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

## Finding Lean declarations

When working in an editor or agent session, use the Lean LSP for Lean-specific
lookup before falling back to text search. Declaration search gives the
namespace-qualified name, hover information gives the elaborated type and
documentation, and reference search finds existing uses. Goal and diagnostic
queries are also useful when a ported theorem appears not to apply. This keeps
lookup aware of namespaces, notation, implicit arguments, and generated
declarations. Use `rg`/`grep` for HOL/SML source references and broad
repository-text searches, where LSP cannot help.

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
global initialization, ordinary memory loads, and a deterministic FFI service
boundary. They deliberately do not rely only on a Flapjack correctness
theorem: distinct compilers can satisfy the same source theorem while emitting
different code. The checked-in 22-fixture source corpus is currently
byte-exact; broader accepted-program coverage and differential-fuzz findings
remain open follow-up work. These
fixtures are stable seeds for differential fuzzing against `cake`; a source
accepted by CakeML but not executable by Flapjack is a P1 compiler-parity bug.

For the checked-in source-to-RISC-V artifact corpus, run
`scripts/parity-small-corpus.py`. It invokes both `cake` and
`flapjack-compile --assembly`, checks the pinned Cake output hashes, compares
runtime/entry/user sections without hiding byte differences, and succeeds only
when every residual difference has an owning bead. This artifact audit
complements the machine-execution fixture above; it does not replace it.

## Differential fuzzing against `cake`

`scripts/parity-difffuzz.py` is a deterministic differential fuzzer over the
same boundary. It generates Pancake sources from a fixed grammar (or
deterministically mutates the checked-in `Flapjack/Test/OriginalPancake`
corpus), runs both compilers under `nice -n 10 timeout 20s`, and compares
acceptance, diagnostics class, section names and order, entry addresses,
section bytes, runtime-image metadata, and the static frame - not only
acceptance. The only normalization is the documented `cml_` prefix and
`_<digits>` suffix strip on section names.

Every mismatch is classified into a signature (`sections/order`,
`bytes/user:main:len_ne`, `frame/bitmap-table`, `acceptance/gap:entry`, ...).
The current gaps registry is intentionally empty: all previously recorded
acceptance and frame signatures have been fixed. If a new temporary
exception is ever required, it must be owned by an active bead and listed in
[`scripts/parity-difffuzz-gaps.json`](../scripts/parity-difffuzz-gaps.json);
acceptance disagreements and tool failures are never owned, so they always
surface. Unknown signatures and CakeML-accepted/Flapjack-rejected cases exit
nonzero, and each such finding is written
under `--out` with the source, both outputs, tool versions (binary sha256 +
git commit), exact command lines, and a standalone `replay.sh`, then
delta-debugged with `--minimize` and filed as a P1 bead.

Typical bounded runs (each a few minutes, safe for a laptop):

```sh
nice -n 10 python3 scripts/parity-difffuzz.py --smoke --exact # every accepted artifact must match
nice -n 10 python3 scripts/parity-difffuzz.py --smoke --include-globals --exact
nice -n 10 python3 scripts/parity-difffuzz.py --mode mixed --exact --seed 3 --count 80 \
    --out difffuzz-findings --minimize                      # bounded exact campaign
python3 scripts/parity-difffuzz.py --mode mixed --seed 3 --count 80 \
    --out difffuzz-findings --minimize                      # bounded campaign
python3 scripts/parity-difffuzz.py --replay difffuzz-findings/<case>
```

The `--include-globals` variant adds deterministic global declarations and
global-based load/store addresses to generated cases.  It is kept as a
separate smoke invocation so the ordinary campaign remains directly
comparable with older recorded seeds.  Run it in an environment with both
the original CakeML `cake` binary and Flapjack; CI uses the checked-in
artifact corpus (which includes global fixtures) because it does not build
the CakeML reference binary.

`--exact` is the required mode for source-to-RISC-V parity: any difference in
acceptance, section layout, metadata, or bytes is a failure, including a
signature listed in the historical bead-owned gap registry. The mode without
`--exact` is retained only for auditing older campaigns and must not be used
as evidence that the two compilers emit identical output.

Minimized, replayable reproducers for the found mismatches are preserved under
[`scripts/parity-difffuzz-findings/`](../scripts/parity-difffuzz-findings)
(one directory per owning bead). Do not put unbounded fuzzing into CI; the
smoke corpus is the small deterministic check.

## Reducing a discrepancy

A discrepancy found on a large input is usually unreadable. Shrink it first
with the delta-debugging reducer described in
[`PARITY-REDUCING.md`](PARITY-REDUCING.md):

```sh
lake build flapjack-compile
python3 scripts/parity-reduce.py CASE.pnk --out /tmp/reduction
```

It preserves the discrepancy the seed exhibits, writes the minimized source and
a `replay.sh` that doubles as a regression check, and reimplements no part of
the oracle. Keep reductions of large inputs outside the repository until they
are reviewed as fixtures.

## Debugging a discrepancy

Use [`scripts/parity-debug.py`](../scripts/parity-debug.py) for a single
reproducer. It saves the source, both final assembly frames, compiler stderr,
a machine-readable comparison, and a unified final-output diff in one
directory:

```sh
python3 scripts/parity-debug.py scripts/parity-difffuzz-findings/dup-global/case.pnk \
    --out /tmp/dup-global-debug --minimize
```

The optional `--minimize` pass is a bounded, signature-preserving delta
debugger. It removes source lines only when Cake and Flapjack retain exactly
the same acceptance/artifact mismatch signature. `case.min.pnk` is therefore
a useful repro, but it must still be reviewed for readability and semantic
intent before being checked in. This is the repository's small, reproducible
analogue of C-Reduce; it does not invoke arbitrary source transformations
that might accidentally change the language category being tested.

After shrinking, limit the Flapjack dump to one source-level function when the
section name is already known:

```sh
python3 scripts/parity-debug.py CASE.pnk --out /tmp/debug --minimize \
    --function _mpt_delete_node_body
```

The function filter applies to the Lean dump; the Cake/HOL dump remains the
complete probe output so that the surrounding pass context is not lost.

The same command also captures intermediate values from both implementations.
With `--minimize`, it shrinks the source before producing the final assembly
or intermediate-stage dumps; the original input is retained as `case.pnk`, and
the witness used for the dumps is recorded as `comparison_source` in
`comparison.json`.
`flapjack-stages.txt` comes from `lake exe flapjack-debug`, while
`cake-stages.txt` comes from the original HOL definitions through
[`scripts/hol-probes/pancake-stage-probeScript.sml`](../scripts/hol-probes/pancake-stage-probeScript.sml).
When `--minimize` is supplied, both stage dumps are run on the resulting
`case.min.pnk`, not the original large input; `comparison.json` records that
stage source explicitly.
The stage sequence is the original `pan_simp`, `pan_structs`, `pan_globals`,
`pan_to_crep`, `crep_to_loop`, and `loop_to_word` boundary. Compare matching
stage records first; the first divergence identifies the pass that should be
ported or repaired. The HOL stage capture requires a built HOL4/CakeML tree,
but final artifacts and the Lean dump remain available without it.

For allocator discrepancies, set `PANCAKE_ALLOCATOR_PROBE=1` when running the
HOL probe. Set `PANCAKE_ALLOCATOR_LABEL=66` (or another numeric Word label)
to inspect that function's original post-cleanup allocator input, heuristics,
and stack-only set without rendering allocator data for the whole program.
For any intermediate-stage investigation, also set `PANCAKE_STAGE_LABEL=258`
(the numeric function label of interest). This filters the original
`crep_to_loop` result before `loop_to_word`, avoiding multi-gigabyte dumps for
large guests; it can be combined with the allocator probe.

For a relocation or stored-length discrepancy after `loop_to_word`, use
`flapjack-debug --lab-label LABEL CASE.pnk`. It prints only the selected
source-shaped Lab section at the `initial`, `encoded`, `relabelled`, and
`final` linker stages, including each line's stored length and byte position.
The label is the numeric section name shown by the Lean stage dump; this
compact view avoids rendering the complete linked program. Compare it with
the CakeML `enc_sec_list`/`enc_secs_again` probe before changing relocation or
padding code.

For a larger campaign, preserve the complete finding directory produced by
`parity-difffuzz.py --out ... --minimize` and then run `parity-debug.py` on its
`case.min.pnk`. This keeps fuzzing, shrinking, stage inspection, and review
evidence separate while retaining exact replay commands and tool provenance.

## Review and Beads

Keep the porting Bead open until the original evidence and the Lean test are
both present. Record the branch and commit in the Bead while work is in
progress. Agents share the combined PR, merge the coordinator's current head
before starting a new slice, and report every content commit so the combined
branch remains reproducible.

This workflow concerns implementation parity and regression evidence. The
validity and implications of theorems, including the still-parameterized
top-level compiler-correctness boundary, are documented separately in
[`SOUNDNESS.md`](SOUNDNESS.md).
