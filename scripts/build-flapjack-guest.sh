#!/usr/bin/env bash
# build-flapjack-guest.sh COMMIT OUT_DIR
#
# Fetches the pinned "stateless guest" Pancake source (the same
# `Guest/guest.pp.pnk` already pinned by scripts/check-guest-parity.py and
# .github/workflows/lean_action_ci.yml) and its runtime linkage shim from the
# `pirapira/stateless-pancaketh` repo at COMMIT, then compiles it with
# flapjack's own `flapjack-compile` into a bootable RISC-V ELF.
#
# This is the same recipe as that repo's `guest/build.sh`, with `cake`
# replaced by `flapjack-compile` -- the recipe is exactly what makes the
# resulting ELF obey "the evm-asm stateless-guest contract" (fixed input/
# output addresses at 0x40000000 / 0xa0010000, halt via ecall a7=93; see the
# fetched runtime/start.S). Because scripts/check-guest-parity.py already
# proves `flapjack-compile --assembly` is byte-identical to `cake`'s output
# for this exact source, linking flapjack's assembly with this recipe
# produces a byte-identical ELF to the one `guest/build.sh` would produce.
#
# Usage:
#   scripts/build-flapjack-guest.sh COMMIT OUT_DIR
#
# Environment:
#   FLAPJACK   path to the flapjack-compile executable
#              (default: .lake/build/bin/flapjack-compile)
#   RISCV_AS   RISC-V assembler (default: riscv64-unknown-elf-as)
#   RISCV_LD   RISC-V linker    (default: riscv64-unknown-elf-ld)
#   CPP        C preprocessor, used on flapjack's asm output the same way
#              cake's own `.S` needs it (default: cpp)
#
# Output (under OUT_DIR):
#   guest.pp.pnk       -- fetched guest source (sha256-pinned)
#   start.S            -- fetched runtime shim
#   guest.flapjack.S   -- flapjack-compile's raw assembly output
#   guest.flapjack.elf -- the linked, bootable guest
set -euo pipefail
cd "$(dirname "$0")/.."

COMMIT="${1:?usage: scripts/build-flapjack-guest.sh COMMIT OUT_DIR}"
OUT_DIR="${2:?usage: scripts/build-flapjack-guest.sh COMMIT OUT_DIR}"
REPO="pirapira/stateless-pancaketh"

FLAPJACK="${FLAPJACK:-.lake/build/bin/flapjack-compile}"
AS="${RISCV_AS:-riscv64-unknown-elf-as}"
LD="${RISCV_LD:-riscv64-unknown-elf-ld}"
CPP="${CPP:-cpp}"

if [[ ! -x "$FLAPJACK" ]]; then
  echo "flapjack-compile not found/executable at $FLAPJACK -- run: lake build flapjack-compile" >&2
  exit 1
fi

# Single source of truth for the pinned guest source hash: parsed out of
# check-guest-parity.py rather than duplicated, so the two can never drift.
EXPECTED_SOURCE_SHA256="$(grep -oE '"[0-9a-f]{64}"' scripts/check-guest-parity.py | head -1 | tr -d '"')"
if [[ -z "$EXPECTED_SOURCE_SHA256" ]]; then
  echo "could not read EXPECTED_SOURCE_SHA256 out of scripts/check-guest-parity.py" >&2
  exit 1
fi

mkdir -p "$OUT_DIR"
src="$OUT_DIR/guest.pp.pnk"
runtime="$OUT_DIR/start.S"

echo "==> fetching guest source + runtime shim from $REPO@$COMMIT"
curl -fsSL "https://raw.githubusercontent.com/$REPO/$COMMIT/Guest/guest.pp.pnk" -o "$src"
curl -fsSL "https://raw.githubusercontent.com/$REPO/$COMMIT/guest/runtime/start.S" -o "$runtime"

actual_sha256="$(sha256sum "$src" | cut -d' ' -f1)"
if [[ "$actual_sha256" != "$EXPECTED_SOURCE_SHA256" ]]; then
  echo "guest.pp.pnk sha256 mismatch at $REPO@$COMMIT:" >&2
  echo "  expected $EXPECTED_SOURCE_SHA256" >&2
  echo "  got      $actual_sha256" >&2
  echo "This must match scripts/check-guest-parity.py's EXPECTED_SOURCE_SHA256 -- update the pinned commit and that constant together, not separately." >&2
  exit 1
fi

echo "==> flapjack-compile --assembly"
"$FLAPJACK" --assembly "$src" > "$OUT_DIR/guest.flapjack.S"

echo "==> assemble + link"
"$CPP" -P -x assembler-with-cpp "$OUT_DIR/guest.flapjack.S" > "$OUT_DIR/guest.flapjack.s"
"$AS" -march=rv64imac -mno-relax -o "$OUT_DIR/guest.flapjack.o" "$OUT_DIR/guest.flapjack.s"
"$AS" -march=rv64imac_zicsr -mno-relax -o "$OUT_DIR/start.o" "$runtime"
"$LD" -Ttext=0x80000000 -Tdata=0xa0020000 -nostdlib --no-relax -e _start \
  -o "$OUT_DIR/guest.flapjack.elf" "$OUT_DIR/start.o" "$OUT_DIR/guest.flapjack.o"

echo "==> built $OUT_DIR/guest.flapjack.elf"
sha256sum "$OUT_DIR/guest.flapjack.elf"
