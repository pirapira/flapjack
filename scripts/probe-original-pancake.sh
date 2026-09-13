#!/usr/bin/env bash
set -euo pipefail

# Regenerate a checked-in Pancake probe artifact:
#   scripts/probe-original-pancake.sh INPUT.pnk OUTPUT.cake.S
# The default can be overridden when testing another CakeML checkout.
cake_bin="${CAKE_BIN:-cakeml/developers/bin/cake}"

if [[ $# -ne 2 ]]; then
  echo "usage: $0 INPUT.pnk OUTPUT.cake.S" >&2
  exit 2
fi

exec "$cake_bin" --pancake --target=riscv < "$1" > "$2"
