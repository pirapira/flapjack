# Preserved differential-fuzz findings (minimized)

Minimized, replayable reproducers for the mismatches found by
`scripts/parity-difffuzz.py` (differential fuzzing of original Pancake
`cake` vs `flapjack-compile`). Each directory holds one finding:

| directory        | signatures                                              | owning bead (P1)                |
|------------------|---------------------------------------------------------|---------------------------------|
| `bitmap-min/`    | `frame/bitmap-table` (+ known lowering sigs)            | `flapjack-pxn.8.5.14.1`         |
| `ffi-min/`       | `frame/ffi-stub` (+ known lowering sigs)                | `flapjack-pxn.8.5.14.2`         |
| `nomain-global/` | `acceptance/gap:entry` (cake accepts, flapjack rejects) | `flapjack-pxn.8.5.14.3`         |
| `dup-global/`    | `acceptance/gap:other` (duplicate global redeclared)    | `flapjack-pxn.8.5.14.4`         |

Each directory contains:

- `case.pnk` - the minimized Pancake source;
- `cake.S` / `cake.err`, `flapjack.S` / `flapjack.err` - captured outputs;
- `finding.json` - signatures, normalized comparison details, tool
  versions (binary sha256 + git commit), exact command lines, return codes;
- `replay.sh` - standalone re-run script.

## Replaying

    python3 scripts/parity-difffuzz.py --replay scripts/parity-difffuzz-findings/bitmap-min

re-runs `case.pnk` through both compilers and checks that the recorded
signatures still reproduce (exit 0 on match). Signatures that stop
reproducing mean the underlying bead has been fixed.

## Regenerating

The directories are plain outputs of the harness and can be regenerated
deterministically from the saved sources:

    python3 scripts/parity-difffuzz.py \
        --file scripts/parity-difffuzz-findings/<name>/case.pnk \
        --out scripts/parity-difffuzz-findings

The `acceptance/gap:*` directories belong to beads by construction: the
gaps registry (`scripts/parity-difffuzz-gaps.json`) never marks acceptance
signatures as known, so any re-run of these sources surfaces them again as
findings until the owning beads are fixed.
