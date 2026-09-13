#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/../.." && pwd)
hol_dir=${HOL4:-/home/zksecurity/HOL}
cake_dir=${CAKEML:-"$repo_dir/cakeml"}

if [[ ! -x "$hol_dir/bin/Holmake" ]]; then
  echo "HOL4 Holmake not found: $hol_dir/bin/Holmake" >&2
  exit 2
fi
if [[ ! -f "$cake_dir/pancake/loop_to_wordScript.sml" ]]; then
  echo "CakeML Pancake source not found: $cake_dir/pancake/loop_to_wordScript.sml" >&2
  exit 2
fi

probe_dir="$repo_dir/scripts/hol-probes"
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

# Run from Pancake's source directory so HOL's ordinary theory loader finds
# the checked-in loop_to_wordTheory objects without modifying the CakeML
# submodule or requiring its CAKEMLDIR project mapping in this repository.
(cd "$cake_dir/pancake" && \
  "$hol_dir/bin/hol" run "$probe_dir/loop_to_word_probeScript.sml") >"$tmp"
sed -n '/^find_var_empty=/,/^find_reg_imm_ctxt=/p' "$tmp" > \
  "$probe_dir/loop_to_word_probe.out"
