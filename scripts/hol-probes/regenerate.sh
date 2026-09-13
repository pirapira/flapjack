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
if [[ ! -f "$cake_dir/pancake/semantics/panSemScript.sml" ]]; then
  echo "CakeML Pancake source not found: $cake_dir/pancake/semantics/panSemScript.sml" >&2
  exit 2
fi
if [[ ! -f "$cake_dir/pancake/semantics/loopSemScript.sml" ]]; then
  echo "CakeML Pancake source not found: $cake_dir/pancake/semantics/loopSemScript.sml" >&2
  exit 2
fi

probe_dir="$repo_dir/scripts/hol-probes"
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

# HOL's `hol run` consumes the already-built CakeML theories; it does not need
# to rebuild an unchanged theory.  Keep the checked-in fixtures incremental as
# well: rerun a probe only when its script, its referenced Pancake source, or
# this driver is newer than the fixture.  This also keeps regeneration quick
# after an ordinary no-op invocation.
probe_needs_refresh() {
  local output="$1"
  local probe="$2"
  local source="$3"
  [[ ! -f "$output" || "$probe" -nt "$output" || \
     "$source" -nt "$output" || "$probe_dir/regenerate.sh" -nt "$output" ]]
}

run_probe() {
  local probe_name="$1"
  local output_name="$2"
  local first_label="$3"
  local last_label="$4"
  local source="$5"
  local probe="$probe_dir/$probe_name"
  local output="$probe_dir/$output_name"
  if probe_needs_refresh "$output" "$probe" "$source"; then
    (cd "$cake_dir/pancake" && \
      "$hol_dir/bin/hol" run "$probe") >"$tmp"
    sed -n "/^${first_label}=/,/^${last_label}=/p" "$tmp" > "$output"
  fi
}

# Run from Pancake's source directory so HOL's ordinary theory loader finds
# the checked-in theory objects without modifying the CakeML submodule or
# requiring its CAKEMLDIR project mapping in this repository.
run_probe loop_to_word_probeScript.sml loop_to_word_probe.out \
  find_var_empty find_reg_imm_ctxt "$cake_dir/pancake/loop_to_wordScript.sml"
run_probe pan_mem_load_probeScript.sml pan_mem_load_probe.out \
  one_hit named_suffix_blocked "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_shape_of_probeScript.sml pan_shape_of_probe.out \
  word nstruct "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_word_helpers_probeScript.sml pan_word_helpers_probe.out \
  is_word the_val_word "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_fixed_load_probeScript.sml pan_fixed_load_probe.out \
  byte_hit load32_unaligned "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe loop_sem_get_vars_probeScript.sml loop_sem_get_vars_probe.out \
  get_vars_hit get_vars_loc "$cake_dir/pancake/semantics/loopSemScript.sml"
# The set_globals probe observes FLOOKUP after the original map update.
run_probe loop_sem_set_globals_probeScript.sml loop_sem_set_globals_probe.out \
  set_globals_new set_globals_sibling "$cake_dir/pancake/semantics/loopSemScript.sml"
