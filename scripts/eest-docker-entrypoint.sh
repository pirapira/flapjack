#!/usr/bin/env bash
# eest-docker-entrypoint.sh -- Docker ENTRYPOINT for the flapjack EEST image.
#
# Runs the EEST "zkevm" conformance fixtures against the flapjack-built
# stateless guest ELF (see scripts/build-flapjack-guest.sh). This reuses
# evm-asm's mature conformance harness
# (evm-asm/scripts/codegen-eest-stateless-check.sh) through its documented
# `--guest-elf` override instead of re-implementing SSZ fixture conversion,
# verdict decoding, and step/budget classification here.
#
# All CMD/args are forwarded to that harness; see its own --help for the
# full option list (--limit, --filter, --steps, --min-succ, ...).
set -euo pipefail
cd "$(dirname "$0")/.."

GUEST_ELF="${FLAPJACK_GUEST_ELF:-$(pwd)/gen-out/guest/guest.flapjack.elf}"
if [[ ! -f "$GUEST_ELF" ]]; then
  echo "flapjack guest ELF not found: $GUEST_ELF" >&2
  echo "  (built at image-build time by scripts/build-flapjack-guest.sh;" >&2
  echo "   set FLAPJACK_GUEST_ELF to point at a different one)" >&2
  exit 1
fi

exec evm-asm/scripts/codegen-eest-stateless-check.sh \
  --guest-elf "$GUEST_ELF" \
  --backend ziskemu \
  --no-verdict-debug \
  "$@"
