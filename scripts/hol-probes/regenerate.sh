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
    sed -n "/^${first_label}=/,/^${last_label}=/p" "$tmp" \
      | sed '/^<<HOL message:/,/^  pattern completion.*>>$/d' > "$output"
  fi
}

# Run from Pancake's source directory so HOL's ordinary theory loader finds
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
run_probe pan_op_probeScript.sml pan_op_probe.out \
  mul_two mul_three "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_fixed_load_probeScript.sml pan_fixed_load_probe.out \
  byte_hit load32_unaligned "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_fixed_store_probeScript.sml pan_fixed_store_probe.out \
  byte_store_hit store32_unaligned "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_flat_store_probeScript.sml pan_flat_store_probe.out \
  store_hit stores_blocked "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_flatten_probeScript.sml pan_flatten_probe.out \
  word named "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_res_var_probeScript.sml pan_res_var_probe.out \
  delete_hit update_hit "$cake_dir/pancake/semantics/panSemScript.sml"
# The pan_primop probe prints numeric w2n values of the returned RStruct.
run_probe pan_sem_pan_primop_probeScript.sml pan_sem_pan_primop_probe.out \
  pan_primop_basic pan_primop_non_word "$cake_dir/pancake/semantics/panSemScript.sml"
# The set_var probe checks local override, unrelated locals, globals, and clock.
run_probe pan_sem_set_var_probeScript.sml pan_sem_set_var_probe.out \
  set_var_new set_var_clock "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_e2e_probeScript.sml pan_sem_e2e_probe.out \
  return_41 return_if_13 "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_e2e_add_probeScript.sml pan_sem_e2e_add_probe.out \
  return_add_6_7 return_add_6_7 "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_call_e2e_probeScript.sml pan_sem_call_e2e_probe.out \
  call_id_7 call_id_7 "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_global_e2e_probeScript.sml pan_sem_global_e2e_probe.out \
  global_g_7 global_g_7 "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_memory_e2e_probeScript.sml pan_sem_memory_e2e_probe.out \
  memory_load_37 memory_load_37 "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_ffi_e2e_probeScript.sml pan_sem_ffi_e2e_probe.out \
  ffi_foo_event ffi_foo_event "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_itree_comp_ffi_probeScript.sml pan_itree_comp_ffi_probe.out \
  ret tau return length_failure final div_ret div_tau \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_trace_prefix_probeScript.sml pan_itree_trace_prefix_probe.out \
  ret final "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_trace_prefix0_probeScript.sml pan_itree_trace_prefix0_probe.out \
  ret final "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_ltree_probeScript.sml pan_itree_ltree_probe.out \
  ret final "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_sh_mem_store_probeScript.sml \
  pan_itree_h_prog_sh_mem_store_probe.out \
  store_zero_width store_final_state \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_probeScript.sml pan_itree_h_prog_probe.out \
  h_prog_skip h_prog_tick "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_sh_mem_load_probeScript.sml \
  pan_itree_h_prog_sh_mem_load_probe.out \
  load_zero_width load_final_locals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_return_probeScript.sml pan_itree_h_prog_return_probe.out \
  return_valid_locals return_invalid "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_raise_probeScript.sml pan_itree_h_prog_raise_probe.out \
  raise_valid_locals raise_invalid "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_ext_call_probeScript.sml pan_itree_h_prog_ext_call_probe.out \
  ext_call_event ext_call_final_locals "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_store_byte_probeScript.sml \
  pan_itree_h_prog_store_byte_probe.out \
  store_byte_success store_byte_domain_error \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_store_32_probeScript.sml \
  pan_itree_h_prog_store_32_probe.out \
  store_32_success store_32_domain_error \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_primitive_probeScript.sml \
  pan_itree_h_prog_primitive_probe.out \
  primitive_success primitive_shape_error \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_set_global_probeScript.sml pan_set_global_probe.out \
  set_global_insert set_global_locals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_evaluate_probeScript.sml pan_itree_evaluate_probe.out \
  itree_evaluate_skip itree_evaluate_tick \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_ext_probeScript.sml pan_ext_probe.out \
  ext_ffi ext_locals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_set_kvar_probeScript.sml pan_set_kvar_probe.out \
  set_kvar_local set_kvar_global_locals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_lookup_kvar_probeScript.sml pan_lookup_kvar_probe.out \
  lookup_kvar_local lookup_kvar_missing \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_is_valid_value_probeScript.sml pan_is_valid_value_probe.out \
  is_valid_value_local is_valid_value_mismatch \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_eval_probeScript.sml pan_eval_probe.out \
  eval_const eval_missing \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_dec_probeScript.sml pan_itree_h_prog_dec_probe.out \
  dec_valid_event dec_failed_response "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_seq_probeScript.sml pan_itree_h_prog_seq_probe.out \
  seq_second_event seq_second_normal "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_cond_probeScript.sml pan_itree_h_prog_cond_probe.out \
  cond_true_branch cond_failed_source "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_store_probeScript.sml pan_itree_h_prog_store_probe.out \
  store_success store_invalid_value "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_assign_probeScript.sml pan_itree_h_prog_assign_probe.out \
  assign_valid assign_failed_eval "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_while_probeScript.sml pan_itree_h_prog_while_probe.out \
  while_zero_guard while_invalid_guard "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe loop_sem_get_vars_probeScript.sml loop_sem_get_vars_probe.out \
  get_vars_hit get_vars_loc "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_get_var_imm_probeScript.sml \
  loop_sem_get_var_imm_probe.out \
  reg_hit reg_loc "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_call_env_probeScript.sml \
  loop_sem_call_env_probe.out \
  arg_zero arg_missing "$cake_dir/pancake/semantics/loopSemScript.sml"
# The locals_touched probe observes the structural Loop expression analysis.
run_probe loop_lang_locals_touched_probeScript.sml \
  loop_lang_locals_touched_probe.out \
  const base_addr "$cake_dir/pancake/loopLangScript.sml"
run_probe loop_lang_assigned_vars_probeScript.sml \
  loop_lang_assigned_vars_probe.out \
  skip load_byte "$cake_dir/pancake/loopLangScript.sml"
run_probe loop_lang_acc_vars_probeScript.sml \
  loop_lang_acc_vars_probe.out \
  skip call_none "$cake_dir/pancake/loopLangScript.sml"
run_probe loop_lang_nested_seq_probeScript.sml \
  loop_lang_nested_seq_probe.out \
  empty assign_load "$cake_dir/pancake/loopLangScript.sml"
run_probe loop_call_is_load_probeScript.sml \
  loop_call_is_load_probe.out \
  load store32 "$cake_dir/pancake/loop_callScript.sml"
run_probe loop_call_comp_probeScript.sml \
  loop_call_comp_probe.out \
  skip fallback_keeps "$cake_dir/pancake/loop_callScript.sml"
# The set_globals probe observes FLOOKUP after the original map update.
run_probe loop_sem_set_globals_probeScript.sml loop_sem_set_globals_probe.out \
  set_globals_new set_globals_sibling "$cake_dir/pancake/semantics/loopSemScript.sml"
# The set_vars probe observes sptree lookups after the original alist_insert.
run_probe loop_sem_set_vars_probeScript.sml loop_sem_set_vars_probe.out \
  set_vars_basic set_vars_clock "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_set_var_probeScript.sml loop_sem_set_var_probe.out \
  set_var_new set_var_missing "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_dec_clock_probeScript.sml loop_sem_dec_clock_probe.out \
  dec_clock_five dec_clock_local "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_fix_clock_probeScript.sml loop_sem_fix_clock_probe.out \
  fix_clock_lower_new fix_clock_zero "$cake_dir/pancake/semantics/loopSemScript.sml"

# The find_code probe observes the returned parameter map via sptree lookups.
run_probe loop_sem_find_code_probeScript.sml loop_sem_find_code_probe.out \
  find_code_label_first find_code_dup_first "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_primop_probeScript.sml loop_sem_primop_probe.out \
  valid_no_carry invalid_nonword "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_mem_store_probeScript.sml loop_sem_mem_store_probe.out \
  mem_store_hit mem_store_other "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_mem_load_probeScript.sml loop_sem_mem_load_probe.out \
  mem_load_hit mem_load_miss "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_eval_probeScript.sml loop_sem_eval_probe.out \
  const top_addr "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_evaluate_probeScript.sml loop_sem_evaluate_probe.out \
  skip tick_timeout "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_semantics_probeScript.sml loop_semantics_probe.out \
  return_clock_zero return_clock_one "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_lprefix_lub_probeScript.sml loop_sem_lprefix_lub_probe.out \
  empty_lub_0 empty_lub_0 "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_cut_state_probeScript.sml loop_sem_cut_state_probe.out \
  hit_first loc_preserved "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_cut_res_probeScript.sml loop_sem_cut_res_probe.out \
  result_short_circuit clock_decrement_and_cut \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_sh_mem_load_probeScript.sml loop_sem_sh_mem_load_probe.out \
  return_zero_width aligned_domain_original_payload \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_sh_mem_store_probeScript.sml loop_sem_sh_mem_store_probe.out \
  store_zero_width aligned_domain_original_payload \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_sh_mem_op_probeScript.sml loop_sem_sh_mem_op_probe.out \
  load store32 "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_exit_loop_probeScript.sml loop_sem_exit_loop_probe.out \
  exit_loop_break exit_loop_error "$cake_dir/pancake/semantics/loopSemScript.sml"
# The loop_arith probe prints numeric word values to avoid raw-literal ambiguity.
run_probe pan_itree_h_handle_call_ret_probeScript.sml \
  pan_itree_h_handle_call_ret_probe.out \
  failed_caller uncaught_exception \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_handle_deccall_ret_probeScript.sml \
  pan_itree_h_handle_deccall_ret_probe.out \
  failed_caller raised_clears_locals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe loop_sem_loop_arith_probeScript.sml loop_sem_loop_arith_probe.out \
  loop_arith_div loop_arith_longdiv_overflow "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe longdiv_code_probeScript.sml longdiv_code_probe.out \
  longdiv_code_software riscv_longdiv_encoding \
  "$cake_dir/compiler/backend/data_to_wordScript.sml"
run_probe pan_itree_h_prog_deccall_probeScript.sml \
  pan_itree_h_prog_deccall_probe.out \
  argument_failure lookup_failure \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_call_probeScript.sml \
  pan_itree_h_prog_call_probe.out \
  argument_failure lookup_failure \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
