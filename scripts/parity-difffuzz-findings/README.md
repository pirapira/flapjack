# Historical differential-fuzz findings (minimized)

These minimized reproducers record mismatches found during earlier
`scripts/parity-difffuzz.py` campaigns between original Pancake `cake` and
`flapjack-compile`. The acceptance and frame discrepancies listed below are
fixed on the current branch; the files remain as regression probes:

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

re-runs `case.pnk` through both compilers. Current behavior should report
`signatures=none` and `reproduced=False`; that is expected for these fixed
historical cases. A newly reproduced signature is a regression.

## Regenerating

The directories are plain outputs of the harness and can be regenerated
deterministically from the saved sources:

    python3 scripts/parity-difffuzz.py \
        --file scripts/parity-difffuzz-findings/<name>/case.pnk \
        --out scripts/parity-difffuzz-findings

The gaps registry (`scripts/parity-difffuzz-gaps.json`) no longer whitelists
frame or acceptance signatures, so any recurrence surfaces as an untracked
finding immediately.
