# Reducing a parity discrepancy

`scripts/parity-reduce.py` is a C-Reduce-style delta-debugging reducer for
Pancake sources. Given a program that exposes a Cake/Flapjack discrepancy it
shrinks the source while the *same* discrepancy survives, so a 16 000-line
guest or a 34-line fuzzer program becomes something a reviewer can read.

It reimplements no part of the oracle. The original CakeML Pancake compiler
and `flapjack-compile` are invoked exactly as
[`scripts/parity-small-corpus.py`](../scripts/parity-small-corpus.py) invokes
them, and the artifact frames are parsed and classified by
[`scripts/parity-bytes.py`](../scripts/parity-bytes.py), so "the same
discrepancy" means what it means everywhere else in this repository. Only the
Python standard library and those scripts are used.

## Running it

```sh
python3 scripts/parity-reduce.py CASE.pnk --out /tmp/reduction
```

Defaults: `cake` at `~/pancake-lean/cakeml/developers/bin/cake` (override with
`--cake` or `$CAKE`), `flapjack-compile` at `.lake/build/bin/flapjack-compile`
(override with `--flapjack` or `$FLAPJACK`). Build the latter first — `lake
build` alone does not rebuild executables:

```sh
lake build flapjack-compile
```

Keep reductions of large inputs outside the repository. A reduced case becomes
a checked-in fixture only after review, through the normal route in
[`PARITY-TESTING.md`](PARITY-TESTING.md): add it under
`Flapjack/Test/OriginalPancake/` and register it in
`scripts/parity-small-corpus.json` with its `cake_sha256`.

## Predicates

`--predicate` selects what must be preserved.

| predicate | holds when |
| --- | --- |
| `signature` (default) | both compilers accept and the set of differing user-section names is exactly the seed's set |
| `mismatch` | both accept and the artifacts differ in any way |
| `section` | both accept and the section named by `--section` still differs |
| `flapjack-reject` | Cake accepts, Flapjack rejects |
| `cake-reject` | Flapjack accepts, Cake rejects |
| `disagree` | exactly one of the two rejects |

`signature` is the default because it is the only one that stops a reduction
from drifting onto a different bug: a shrink step that happens to expose a
second discrepancy, or that replaces the original one, is rejected.
Use `mismatch` when the seed's section set is itself unstable, and the
accept/reject predicates when the discrepancy is that one compiler refuses the
program.

`section` exists for inputs that differ in many places at once. The stateless
guest differs in 676 sections, so requiring all of them to survive prevents any
reduction at all; `--predicate section --section digits_len` reduces towards one
function's discrepancy instead.

Large inputs also need a larger `--timeout`: the default 30 s is below what
`flapjack-compile` takes on the guest, and a timed-out probe is reported as a
seed that does not satisfy the predicate.

## Passes

Each pass is greedy: as soon as a strictly smaller candidate still satisfies
the predicate it becomes the current source, and the pass continues from that
smaller source. Passes run to a fixpoint; the whole sequence repeats until a
full round changes nothing (`--max-rounds`, default 8). This follows the
useful part of C-Reduce's workflow while keeping a deterministic, single-file
reducer for Pancake.

1. **strip comments** — `//` and `/* */` comments and blank lines.
2. **delete-top-level** — delete balanced top-level declaration/statement
   units using a coarse ddmin schedule. This keeps reductions of large guests
   practical by testing whole functions before probing individual lines.
3. **delete-runs** — delete brace-balanced runs of lines, halving the chunk
   size in the usual ddmin schedule. A balanced run is a whole block or a
   smaller statement run, so this pass supplies finer granularity without a
   Pancake parser.
4. **empty-bodies** — replace a function body with a bare `return 0;`.
5. **simplify-expressions** — replace a parenthesised subexpression with `0` or
   `1`. Spans that follow an identifier are skipped, since those are call
   argument lists rather than expressions.
6. **simplify-literals** — shrink an integer literal to `0`, to `1`, to its
   absolute value, or to half its value.

Candidate results are cached by source hash, so a pass that re-proposes a
shape already tried costs nothing.

## Output

`--out` (default `parity-reduction`) receives:

- `case.min.pnk` — the reduced source;
- `report.json` — predicate, seed and reduced sizes, the oracle outcome at both
  ends, per-pass transformation counts, oracle call count, wall time, and the
  sha256 of both compiler binaries;
- `replay.sh` — a standalone check that exits `0` while the discrepancy
  reproduces and `3` once it is gone, so it doubles as a regression check.
  Pass another source as `$1` to check that one instead.

## Worked example

A fuzzer case from the seed-1 campaign
(`scripts/parity-difffuzz.py --seed 1 --count 344`, case index 50), which both
compilers accept and compile to different `main` sections:

```
seed: status=compiled cake_accepted=True flapjack_accepted=True differing=1
seed differing sections: main
reduced 1124 -> 369 bytes (34 -> 21 lines) in 174 oracle calls, 2.2s
passes: delete-runs=13, empty-bodies=0, simplify-expressions=15, simplify-literals=3
```

`replay.sh` on the reduced case exits `0`; on an exact program
(`Flapjack/Test/OriginalPancake/mul_const_zero.pnk`) it exits `3` with
`expected differing sections ['main'] but observed (none)`.

## Harness dry run for the accept/reject predicates

The seed-1 campaign currently reports `opposite=0`, so no real accept/reject
disagreement is available to exercise those predicates end to end. Substituting
a stub that rejects every input drives the same machinery:

```sh
printf '#!/usr/bin/env bash\nexit 1\n' > /tmp/stub-reject.sh
chmod +x /tmp/stub-reject.sh
python3 scripts/parity-reduce.py CASE.pnk \
  --predicate flapjack-reject --flapjack /tmp/stub-reject.sh --out /tmp/dry-run
```

On the case above this reduces 1124 bytes to 29 (`fun 1 main() { return 0; }`)
in 69 oracle calls, exercising `delete-runs` and `empty-bodies`.

## Relation to `parity-difffuzz.py --minimize`

`scripts/parity-difffuzz.py` has a line-level minimizer bounded at 80 steps
that runs inside a campaign on a saved finding directory. This reducer is
standalone, works on any `.pnk` file, is brace-aware, simplifies expressions
and literals as well as deleting lines, and records a replay command. Use the
campaign's minimizer for a quick in-campaign shrink and this one when a case is
going to be read, filed, or turned into a fixture.
