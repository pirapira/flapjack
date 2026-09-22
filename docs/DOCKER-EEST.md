# Running the EEST stateless test against the flapjack-built guest, via Docker

This mirrors [evm-asm's Docker EEST image](https://github.com/Verified-zkEVM/evm-asm/blob/main/DOCKER-EEST.md),
which runs the EEST "zkevm" conformance fixtures against `evm-asm`'s own
Lean-codegen stateless guest. This image runs the *same fixtures* against a
*different guest*: the pinned
[`pirapira/stateless-pancaketh`](https://github.com/pirapira/stateless-pancaketh)
Pancake source, compiled with flapjack's own Pancake-to-RISC-V port
(`flapjack-compile`) instead of `cake` or evm-asm's Lean codegen.

The point of this image is a real, `--all`-scope conformance number for
flapjack's compiler output on a large, real-world guest -- not a synthetic
fixture -- as a complement to the byte-for-byte parity checks in
[`PARITY-TESTING.md`](PARITY-TESTING.md) and
[`../scripts/check-guest-parity.py`](../scripts/check-guest-parity.py).

## What the image contains

- `flapjack-compile`, built from this repo's pinned Lean toolchain
- The pinned `stateless-pancaketh` guest source
  (`Guest/guest.pp.pnk`) and runtime linkage shim (`guest/runtime/start.S`),
  fetched and compiled into `guest.flapjack.elf` by
  [`scripts/build-flapjack-guest.sh`](../scripts/build-flapjack-guest.sh)
- `ziskemu` (ZisK `${ZISK_VERSION}`, installed via `ziskup`; see
  [Supported ZisK version](#supported-zisk-version))
- EEST fixtures (fetched by the vendored
  `evm-asm/scripts/eest-fetch-fixtures.sh`)
- evm-asm's own EEST conformance harness
  (`evm-asm/scripts/codegen-eest-stateless-check.sh`), invoked through its
  documented `--guest-elf` override so this image reuses evm-asm's SSZ
  fixture conversion and verdict-decoding logic rather than reimplementing
  it. evm-asm's own Lean project is **not** built in this image: `--guest-elf`
  implies `--no-build`.

## Pull and run

```bash
# Full run, all fixtures
docker run --rm ghcr.io/pirapira/flapjack-eest:latest

# Focused subset (faster smoke check)
docker run --rm ghcr.io/pirapira/flapjack-eest:latest \
  --filter random_statetest --limit 50
```

`ziskemu` is memory-hungry and the harness forces `--jobs 1` for it
regardless of what is requested (see evm-asm's own script for why); expect a
full `--all` run to take a while.

## Building the image locally

```bash
docker build -t flapjack-eest .

# Override the pinned ZisK version or guest commit
docker build \
  --build-arg ZISK_VERSION=0.18.0 \
  --build-arg STATELESS_PANCAKETH_COMMIT=<sha> \
  -t flapjack-eest .
```

The `evm-asm` git submodule must be initialized first:

```bash
git submodule update --init evm-asm
```

## Supported ZisK version

**ZisK 0.18.0** is the version this image pins (`ARG ZISK_VERSION` in
[`../Dockerfile`](../Dockerfile)) and the minimum known-good version for this
guest. **ZisK 0.16.0 is known not to work** for succinct proof verification
against this guest -- do not downgrade below 0.18.0 without re-validating
end to end.

To bump the pinned version, use
[`scripts/upgrade-zisk.sh`](../scripts/upgrade-zisk.sh):

```bash
scripts/upgrade-zisk.sh 0.19.0
```

This rewrites the `ARG ZISK_VERSION` pin in `Dockerfile`, checks that the
corresponding tag exists upstream, and optionally reinstalls `ziskemu`
locally via `ziskup` to match. It does not touch the (independently pinned)
`STATELESS_PANCAKETH_COMMIT` or EEST fixture tag.

## Guest identity

Because [`scripts/check-guest-parity.py`](../scripts/check-guest-parity.py)
already proves `flapjack-compile --assembly` is byte-identical to `cake`'s
output for this exact pinned guest source, this image's
`guest.flapjack.elf` is byte-identical to what
`stateless-pancaketh`'s own `guest/build.sh` produces from the same source
with `cake`. A conformance regression here is therefore a real difference in
`flapjack-compile`'s output relative to that already-checked baseline, not
guest-selection noise.

## Known caveats

- Building requires the `evm-asm` submodule (`.gitmodules`); it supplies the
  EEST harness scripts only -- its own Lean project, fixtures, and other
  large subdirectories are excluded from the build context via
  `.dockerignore` and are never built or copied into the image.
- `ziskup --nokey` skips the (multi-GB) proving/verify keys. This image only
  emulates the guest under `ziskemu`; it never generates a zk proof.
- The guest source and runtime shim are fetched over the network at image
  build time (not vendored), pinned to a commit SHA for reproducibility.
