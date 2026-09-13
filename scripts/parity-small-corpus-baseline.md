# Small source-to-RISC-V parity baseline

Generated on 2026-09-13 from commit `f6d86d3` with:

```sh
scripts/parity-small-corpus.py --report /var/tmp/flapjack-small-corpus-report.json
```

Both compilers accepted all five fixtures. The original Cake stdout hashes are
also pinned in `parity-small-corpus.json`; the hashes below record the exact
Flapjack assembly frame observed in this run. Runtime sections were equal for
every fixture. Remaining generated-entry/user differences are concrete and
owned by the listed ABI/lowering beads; the runner exits successfully because
there were no untracked discrepancies.

| fixture | Cake stdout SHA-256 | Flapjack stdout SHA-256 | mismatches | owner |
| --- | --- | --- | ---: | --- |
| `empty_locals.pnk` | `e661960e2ea04f6c804fa9487b600bb0289929ba6c76e0dd10f243263cfdd870` | `4f97a5bc6184713977999e52e8322a2cf0df9d677a4e70abe56c4dba4323788e` | 3 | `.8.5.10.1`, `.8.5.10.3` |
| `dec_clock.pnk` | `68281f19fe25699e613b31faebbd8bf54d7e18ad918c04af5ea43f1bc52aa8fa` | `6441ac4fc5b831616d805e622f962ace32cb14731c1c961bebe0b393b87539fa` | 1 | `.8.5.10.1` |
| `crep_op.pnk` | `5e1162c5f80779f9ac072963aac2d3fbbae54d565f05c46a91e4028405dbb57f` | `3475b12363dde885840c5cb835a9ca7e033da1b1070887acf0d199fffed8786b` | 1 | `.8.5.10.1` |
| `set_globals.pnk` | `1281f0d8cd5e1a22486f15baa4a4526e000645f2abec8fb6893e64603b606ac9` | `ac9dc2ca88f12ad2af2dc29dda07e65e4f17478caaccfa080559d395dd7421d6` | 2 | `.8.5.10.2` |
| `set_var.pnk` | `14ee212eefbbc8ba96af33c6372dcde8bc6b2c4babe72779e3124f2df1cd21b1` | `a0682fce10d6e82baac9b0bc53c26a4f5f843b76b0590f1a0403bcaba9000156` | 1 | `.8.5.10.1` |

Summary: `corpus=5 exact=0 tracked_gaps=5 untracked=0`.
