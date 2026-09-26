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
# well: rerun a probe only when its script or its referenced Pancake source is
# newer than the fixture.  Changes to this driver do not invalidate probe
# results, so ordinary harness maintenance stays incremental.
probe_needs_refresh() {
  local output="$1"
  local probe="$2"
  local source="$3"
  [[ ! -f "$output" || "$probe" -nt "$output" || "$source" -nt "$output" ]]
}

run_probe() {
  local probe_name="$1"
  local output_name="$2"
  shift 2
  if [[ -n "${HOL_PROBE_ONLY:-}" && "$probe_name" != "$HOL_PROBE_ONLY" ]]; then
    return 0
  fi
  local labels=()
  while [[ $# -gt 0 ]]; do
    case "$1" in
      /*|\$*) break ;;
      *) labels+=("$1"); shift ;;
    esac
  done
  local first_label=""
  local last_label=""
  if [[ ${#labels[@]} -gt 0 ]]; then
    first_label="${labels[0]}"
    last_label="${labels[${#labels[@]}-1]}"
  fi
  local source="$1"
  shift
  local workdir="${1:-$cake_dir/pancake}"
  local hol_workdir="$workdir"
  if [[ -d "$workdir/.hol/objs" ]]; then
    hol_workdir="$workdir/.hol/objs"
  fi
  local probe="$probe_dir/$probe_name"
  local output="$probe_dir/$output_name"
  if probe_needs_refresh "$output" "$probe" "$source"; then
    (cd "$hol_workdir" && \
      "$hol_dir/bin/hol" run "$probe") >"$tmp"
    if [[ ${#labels[@]} -eq 0 ]]; then
      cp "$tmp" "$output"
    else
      awk -v first="$first_label" -v last="$last_label" '
        BEGIN { started = 0; ended = 0 }
        {
          if (!started) {
            if (index($0, first "=") != 1) next
            started = 1
          } else if (ended && $0 ~ /^[[:alnum:]_]+=/) {
            exit
          }
          if (index($0, last "=") == 1) ended = 1
          print
        }
      ' "$tmp" \
        | sed '/^<<HOL message:/,/^  pattern completion.*>>$/d; /^$/d' > "$output"
    fi
  fi
}

# Run from the local HOL object directory when Holmake has populated it, so
# HOL's ordinary theory loader finds compiled CakeML theories. Fall back to
# the source directory for checkouts whose Holmake places objects there.
run_probe word_add_carry_probeScript.sml word_add_carry_probe.out \
  ordinary carry_overflow "$cake_dir/compiler/backend/backend_commonScript.sml" \
  "$cake_dir/compiler/backend"
run_probe riscv_word_extract_6_probeScript.sml riscv_word_extract_6_probe.out \
  word_extract_6_zero word_extract_6_63 word_extract_6_64_premise \
  "$cake_dir/compiler/encoders/riscv/riscv_targetScript.sml" \
  "$cake_dir/compiler/encoders/riscv"
run_probe riscv_encode_length_probeScript.sml riscv_encode_length_probe.out \
  riscv_encode_length_addi riscv_encode_length_add riscv_encode_length_branch \
  riscv_encode_bytes_addi riscv_encode_bytes_add riscv_encode_bytes_beq \
  riscv_encode_bytes_ld \
  "$cake_dir/compiler/encoders/riscv/riscv_targetScript.sml" \
  "$cake_dir/compiler/encoders/riscv"
run_probe pan_crep_primop_probeScript.sml pan_crep_primop_probe.out \
  pan_valid crep_primop_done "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_structs_opt_mmap_probeScript.sml pan_structs_opt_mmap_probe.out \
  success pointwise "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_compile_correct_probeScript.sml pan_structs_compile_correct_probe.out \
  convert_named_record compile_correct_skip_source compile_correct_skip_converted \
  convert_s_finite_maps \
  compile_correct_tick_zero_source compile_correct_tick_zero_converted \
  compile_correct_tick_positive_source compile_correct_tick_positive_converted \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_compile_exp_correct_probeScript.sml pan_structs_compile_exp_correct_probe.out \
  compile_exp_correct_local_var compile_exp_correct_global_var compile_exp_correct_const \
  compile_exp_correct_mmap_nonempty compile_exp_correct_rstruct \
  compile_exp_correct_rstruct_eval \
  compile_exp_correct_nstruct compile_exp_correct_nfield \
  compile_exp_correct_rfield compile_exp_correct_op compile_exp_correct_load \
  compile_exp_correct_load_out_of_domain \
  compile_exp_correct_load_nested_named \
  compile_exp_correct_load32_le_success \
  compile_exp_correct_load_byte_out_of_domain \
  compile_exp_correct_panop_mul \
  compile_exp_correct_cmp_equal \
  size_of_compile_shape_comb \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"

run_probe semantics_props_implements_probeScript.sml semantics_props_implements_probe.out \
  implements_prime_trans \
  "$cake_dir/semantics/proofs/semanticsPropsScript.sml" \
  "$cake_dir/semantics/proofs"
run_probe pan_structs_mem_load_conversion_probeScript.sml pan_structs_mem_load_conversion_probe.out \
  mem_load_conversion_one mem_load_conversion_comb_multiword \
  mem_load_conversion_named_nested_struct_infos_ok \
  mem_load_conversion_named_nested \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_shape_context_drop_probeScript.sml pan_structs_shape_context_drop_probe.out \
  size_sh_with_ctxt_drop_one size_sh_with_ctxt_drop_named \
  size_sh_with_ctxt_drop_nested_comb \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_value_validity_probeScript.sml pan_structs_value_validity_probe.out \
  v_flds_ok_word v_flds_ok_named_match v_flds_ok_named_mismatch \
  v_flds_ok_named_missing v_flds_ok_duplicate_first \
  is_wf_shape_v_word is_wf_shape_v_named_match \
  is_wf_shape_v_named_missing v_flds_ok_append_nonempty_prefix_named \
  value_validity_done \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_afindi_map_probeScript.sml pan_structs_afindi_map_probe.out \
  hit_preserves_key_index missing_key_stays_missing \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_afindi_length_probeScript.sml pan_structs_afindi_length_probe.out \
  first_match_strictly_below_length last_match_strictly_below_length \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_afindi_el_probeScript.sml pan_structs_afindi_el_probe.out \
  first_match_fst middle_match_fst last_match_fst \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_alookup_afindi_probeScript.sml pan_structs_alookup_afindi_probe.out \
  present_lookup_projection missing_lookup_projection duplicate_key_first_value \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_afindi_append_probeScript.sml pan_structs_afindi_append_probe.out \
  prefix_hit_keeps_first_index suffix_hit_adds_prefix_length missing_key_stays_none \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_structs_dropwhile_afindi_probeScript.sml pan_structs_dropwhile_afindi_probe.out \
  first_hit_drop later_hit_drop missing_hit_drop \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe loop_to_word_probeScript.sml loop_to_word_probe.out \
  find_var_empty find_reg_imm_ctxt "$cake_dir/pancake/loop_to_wordScript.sml"
# The get_stack_only probe observes the allocator driver's stack-only
# analysis over wordLang programs (backend word_alloc).
run_probe get_stack_only_probeScript.sml get_stack_only_probe.out \
  skip assign_leaf "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe pan_mem_load_probeScript.sml pan_mem_load_probe.out \
  one_hit named_suffix_blocked "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_state_eval_probeScript.sml pan_sem_state_eval_probe.out \
  word_load_hit pan_sem_state_eval_done \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_shape_of_probeScript.sml pan_shape_of_probe.out \
  word nstruct "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_evaluate_decls_probeScript.sml pan_evaluate_decls_probe.out \
  empty exn_bad_shape_failure "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_word_helpers_probeScript.sml pan_word_helpers_probe.out \
  is_word the_val_word "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_op_probeScript.sml pan_op_probe.out \
  mul_two mul_three "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_fixed_load_probeScript.sml pan_fixed_load_probe.out \
  mem_load_byte_definition load32_width24_address4 \
  "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_fixed_store_probeScript.sml pan_fixed_store_probe.out \
  byte_store_hit store32_unaligned "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe crep_runtime_word_boundary_probeScript.sml crep_runtime_word_boundary_probe.out \
  bytes64 store32_outside "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_ffi_boundary_probeScript.sml crep_runtime_ffi_boundary_probe.out \
  bytes64 set_byte_0_roundtrip "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_shared_domain_probeScript.sml crep_runtime_shared_domain_probe.out \
  valid_zero_mem align_16 "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_arith_dest_const_probeScript.sml crep_arith_dest_const_probe.out \
  constant dimindex_pos "$cake_dir/pancake/crep_arithScript.sml"
run_probe crep_state_mapc_probeScript.sml crep_state_mapc_probe.out \
  fmap_map2_keyed_lookup \
  "$hol_dir/src/finite_maps/finite_mapScript.sml" \
  "$hol_dir/src/finite_maps"
run_probe crep_arith_lookup_code_probeScript.sml crep_arith_lookup_code_probe.out \
  simp_prog_after_lookup \
  "$cake_dir/pancake/proofs/crep_arithProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_arith_eval_mul_const_probeScript.sml crep_arith_eval_mul_const_probe.out \
  input_word multiply_general "$cake_dir/pancake/proofs/crep_arithProofScript.sml"
run_probe crep_runtime_read_bytes_probeScript.sml crep_runtime_read_bytes_probe.out \
  read_bytes_zero read_bytes_out_of_domain "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_write_bytes_probeScript.sml crep_runtime_write_bytes_probe.out \
  write_head write_fallback_discards_tail "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_ext_call_probeScript.sml crep_runtime_ext_call_probe.out \
  empty_name_identity oracle_diverged "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_runtime_shared_mem_probeScript.sml crep_runtime_shared_mem_probe.out \
  load_returned store_final "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_every_exp_probeScript.sml crep_every_exp_probe.out \
  const_hit always_op_nested "$cake_dir/pancake/semantics/crepPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_assigned_vars_probeScript.sml crep_assigned_vars_probe.out \
  afv_prog nested_afv "$cake_dir/pancake/semantics/crepPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_dec_clock_simp_probeScript.sml crep_dec_clock_simp_probe.out \
  dec_clock_clock empty_locals_memory "$cake_dir/pancake/semantics/crepPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_to_loop_state_rel_probeScript.sml crep_to_loop_state_rel_probe.out \
  memaddrs_mdomain_mem clock_mismatch "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_globals_rel_probeScript.sml crep_to_loop_globals_rel_probe.out \
  wlab_wloc_word globals_lookup_absent "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_mem_rel_probeScript.sml crep_to_loop_mem_rel_probe.out \
  mem_rel_match mem_rel_dom_absent "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_distinct_funcs_probeScript.sml crep_to_loop_distinct_funcs_probe.out \
  distinct_funcs_sep distinct_funcs_absent "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_distinct_vars_probeScript.sml crep_to_loop_distinct_vars_probe.out \
  distinct_vars_sep distinct_vars_absent "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_ctxt_max_probeScript.sml crep_to_loop_ctxt_max_probe.out \
  ctxt_max_within ctxt_max_absent "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_locals_rel_probeScript.sml crep_to_loop_locals_rel_probe.out \
  ctxt_vars_lookup subset_domain_component \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_locals_insert_probeScript.sml crep_to_loop_locals_insert_probe.out \
  insert_same subset_preserved \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_locals_cutset_probeScript.sml crep_to_loop_locals_cutset_probe.out \
  cutset_sub_0 cutset_domain_trans \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_mem_lookup_probeScript.sml crep_to_loop_mem_lookup_probe.out \
  ml_hit ml_distinct \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_list_insert_probeScript.sml crep_to_loop_list_insert_probe.out \
  li_mem_3 li_snoc_agrees \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_insert_insert_probeScript.sml crep_to_loop_insert_insert_probe.out \
  iie_hit iie_agrees_deep \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_list_insert2_probeScript.sml crep_to_loop_list_insert2_probe.out \
  lii_ty_nonmember lia_absent \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_assigned_vars_mapidx_probeScript.sml crep_to_loop_assigned_vars_mapidx_probe.out \
  avma_nil avma_offset_zero \
  "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe loop_props_assigned_vars_probeScript.sml loop_props_assigned_vars_probe.out \
  avs_seq_split avs_nested_assign_three \
  "$cake_dir/pancake/semantics/loopPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_to_loop_context_defs_probeScript.sml crep_to_loop_context_defs_probe.out \
  find_var_hit find_lab_miss "$cake_dir/pancake/crep_to_loopScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_mk_ctxt_probeScript.sml crep_to_loop_mk_ctxt_probe.out \
  mk_ctxt_vars make_vmap_empty_miss "$cake_dir/pancake/crep_to_loopScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_make_vmap_dup_probeScript.sml crep_to_loop_make_vmap_dup_probe.out \
  mvd_single_hit mvd_dup_last_wins "$cake_dir/pancake/crep_to_loopScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_rt_vars_distinct_probeScript.sml crep_to_loop_rt_vars_distinct_probe.out \
  acd_distinct acd_missing "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_map_map2_fst_probeScript.sml crep_to_loop_map_map2_fst_probe.out \
  mm2_pair_eq mm2_empty "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_alookup_el_probeScript.sml crep_to_loop_alookup_el_probe.out \
  ael_shape_0 ael_result "$cake_dir/pancake/proofs/crep_to_loopProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_make_funcs_probeScript.sml crep_to_loop_make_funcs_probe.out \
  mkf_f mkf_dup_first "$cake_dir/pancake/crep_to_loopScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_to_loop_helpers_probeScript.sml crep_to_loop_helpers_probe.out \
  gen_temps_3 rt_vars_absent "$cake_dir/pancake/crep_to_loopScript.sml" \
  "$cake_dir/pancake"
run_probe fm_empty_zip_alist_probeScript.sml fm_empty_zip_alist_probe.out \
  fold_flookup_eq zip_lookup_witness "$cake_dir/pancake/semantics/pan_commonPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_common_props_no_overlap_probeScript.sml pan_common_props_no_overlap_probe.out \
  slot_nodup_x nested_zip_lookup "$cake_dir/pancake/semantics/pan_commonPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_common_distinct_lists_probeScript.sml pan_common_distinct_lists_probe.out \
  distinct_true distinct_eq_disjoint genlist_vmax_bound genlist_vmax_hit \
  genlist_vmax_disjoint "$cake_dir/pancake/pan_commonScript.sml" \
  "$cake_dir/pancake"
run_probe word_to_stack_bits_to_word_probeScript.sml word_to_stack_bits_to_word_probe.out \
  bits_empty wordlist_chunk "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_word_list_probeScript.sml word_to_stack_word_list_probe.out \
  wl_empty_d3 wl_twostep "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_chunk_to_bits_probeScript.sml word_to_stack_chunk_to_bits_probe.out \
  cb_empty cb_ignores_word "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_chunk_to_bitmap_probeScript.sml word_to_stack_chunk_to_bitmap_probe.out \
  cbm_empty cwb_split8 "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_write_bitmap_probeScript.sml word_to_stack_write_bitmap_probe.out \
  wb_empty wb_order_eq "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_insert_bitmap_probeScript.sml word_to_stack_insert_bitmap_probe.out \
  ib_empty ib_new_len "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_stack_slots_probeScript.sml word_to_stack_stack_slots_probe.out \
  ss_num_stack_ret_pair ss_stack_free_inl "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_perf_slots_probeScript.sml word_to_stack_perf_slots_probe.out \
  ps_perf_rsp ps_handler_slots_false "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_to_stack_reg_format_probeScript.sml word_to_stack_reg_format_probe.out \
  rf_reg1_high wma_two "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
run_probe stack_lang_prog_combinators_probeScript.sml stack_lang_prog_combinators_probe.out \
  lc_empty wss_two "$cake_dir/compiler/backend/stackLangScript.sml" \
  "$cake_dir/compiler/backend"
run_probe stack_lang_store_name_probeScript.sml stack_lang_store_name_probe.out \
  sn_count sn_temp_word_bits "$cake_dir/compiler/backend/stackLangScript.sml" \
  "$cake_dir/compiler/backend"
run_probe asm_inst_fragment_probeScript.sml asm_inst_fragment_probe.out \
  ar_reg as_loc "$cake_dir/compiler/encoders/asm/asmScript.sml" \
  "$cake_dir/compiler/encoders/asm"
run_probe pan_props_alist_probeScript.sml pan_props_alist_probe.out \
  alist_a_nodup alist_duplicate_first "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_props_alist_ctxt_max_probeScript.sml pan_props_alist_ctxt_max_probe.out \
  ctxt_a_bound ctxt_duplicate_first_bound "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_props_list_rel_probeScript.sml pan_props_list_rel_probe.out \
  len0 flookup0 "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_inline_code_inl_probeScript.sml crep_inline_code_inl_probe.out \
  flookup_f skip_identity "$cake_dir/pancake/crep_inlineScript.sml" \
  "$cake_dir/pancake"
run_probe crep_inline_alist_map_probeScript.sml crep_inline_alist_map_probe.out \
  alist_duplicate_first input_rows_order "$cake_dir/pancake/crep_inlineScript.sml" \
  "$cake_dir/pancake"
run_probe crep_inline_helper_probeScript.sml crep_inline_helper_probe.out \
  eoc_p unreach_p "$cake_dir/pancake/crep_inlineScript.sml" "$cake_dir/pancake"
run_probe crep_inline_cont_res_probeScript.sml crep_inline_cont_res_probe.out \
  cont_res_none cont_res_done "$cake_dir/pancake/proofs/crep_inlineProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe crep_inline_eval_probeScript.sml crep_inline_eval_probe.out \
  src_main_is_call continue_eval "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe pan_flat_store_probeScript.sml pan_flat_store_probe.out \
  store_hit stores_blocked "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_flatten_probeScript.sml pan_flatten_probe.out \
  word named "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_lang_nested_seq_probeScript.sml pan_lang_nested_seq_probe.out \
  empty assign_seq "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_exp_ids_probeScript.sml pan_lang_exp_ids_probe.out \
  empty fallback "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_with_shape_probeScript.sml pan_lang_with_shape_probe.out \
  empty_shapes short_input "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_wf_fields_context_probeScript.sml pan_lang_wf_fields_context_probe.out \
  empty_fields self_reference_context "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_wf_shape_probeScript.sml pan_lang_wf_shape_probe.out \
  one nested_unknown "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_size_of_sh_with_ctxt_probeScript.sml pan_lang_size_of_sh_with_ctxt_probe.out \
  one known_named missing_named nested_comb nested_named_size_drop \
  "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_size_of_shape_probeScript.sml pan_lang_size_of_shape_probe.out \
  one empty_comb named nested_comb "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_decl_predicates_probeScript.sml pan_lang_decl_predicates_probe.out \
  is_decl_decl is_decl_exception is_exn_decl_exception is_exn_decl_decl \
  is_name_name is_name_decl size_of_eids_empty size_of_eids_mixed \
  "$cake_dir/pancake/panLangScript.sml"
run_probe compile_shape_probeScript.sml compile_shape_probe.out \
  one compile_shapes_map compiled_shape_wf compiled_shapes_wf \
  "$cake_dir/pancake/pan_structsScript.sml"
run_probe pan_lang_var_exp_probeScript.sml pan_lang_var_exp_probe.out \
  local_var global_var nested nested_global "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_load_store_op_probeScript.sml pan_lang_load_store_op_probe.out \
  load_op8 load_op16 load_opw load_op32 store_op8 store_op16 store_opw store_op32 \
  "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_is_function_probeScript.sml pan_lang_is_function_probe.out \
  function global "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_functions_probeScript.sml pan_lang_functions_probe.out \
  empty function global "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_exceptions_probeScript.sml pan_lang_exceptions_probe.out \
  empty exception "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_fun_ids_probeScript.sml pan_lang_fun_ids_probe.out \
  empty call handler dec_call "$cake_dir/pancake/panLangScript.sml"
run_probe word_stack_frame_probeScript.sml word_stack_frame_probe.out \
  maxvar_skip limit_seq later_pair_f later_pair_alloc later_pair_slot_44 \
  later_pair_slot_46 later_pair_bounded \
  "$cake_dir/compiler/backend/word_to_stackScript.sml"
run_probe word_stack_max_var_probeScript.sml word_stack_max_var_probe.out \
  maxvar_inst_mem maxvar_return "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_alloc_cost_probeScript.sml word_alloc_cost_probe.out \
  spill_zero spill_c1 spill_lr1 spill_lm1 spill_rr1 spill_rm1 spill_all1 \
  spill_all1_tail coal_empty coal_x_in coal_y_in coal_both_in coal_pri2_both_in \
  "$cake_dir/compiler/backend/word_allocScript.sml" "$cake_dir/compiler/backend"
run_probe pan_lang_free_var_ids_probeScript.sml pan_lang_free_var_ids_probe.out \
  empty global_in_handler "$cake_dir/pancake/panLangScript.sml"
run_probe pan_lang_inlinable_probeScript.sml pan_lang_inlinable_probe.out \
  inline_true non_function "$cake_dir/pancake/panLangScript.sml"
run_probe get_forced_probeScript.sml get_forced_probe.out \
  add_carry nested "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
# The mk_bij probe observes the clash-tree-to-node bijection used to number
# allocator nodes (reads before writes, seq right-first, branch live sets).
run_probe mk_bij_probeScript.sml mk_bij_probe.out \
  delta_basic composite "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe reg_alloc_dec_deg_probeScript.sml reg_alloc_dec_deg_probe.out \
  dec_deg_in_bounds_result update_degrees_out_of_bounds_result \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend/reg_alloc"
run_probe stack_alloc_next_lab_probeScript.sml stack_alloc_next_lab_probe.out \
  next_lab_skip next_lab_both_continuations \
  "$cake_dir/compiler/backend/stack_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe stack_to_lab_flatten_probeScript.sml stack_to_lab_flatten_probe.out \
  flat_skip flat_tick flat_inst flat_halt flat_seq_tail flat_seq_not_tail \
  flat_if_both_skip flat_if_then_skip flat_if_else_skip \
  flat_if_then_terminates flat_if_else_terminates flat_if_both_live \
  flat_loop_if flat_raise flat_return flat_break flat_continue flat_raw_call \
  flat_call_none_label flat_call_none_reg flat_call_return flat_call_handler \
  flat_jump_lower flat_ffi flat_loc_value flat_install flat_shared_memory \
  flat_code_buffer_write flat_default section_skip section_seq section_if \
  "$cake_dir/compiler/backend/stack_to_labScript.sml" \
  "$cake_dir/compiler/backend"
run_probe lab_props_preconditions_probeScript.sml lab_props_preconditions_probe.out \
  pre_label pre_labasm pre_asmi_skip pre_cbw_to_asm pre_share_to_asm \
  pre_empty_sections pre_label_section pre_skip_asm_section \
  "$cake_dir/compiler/backend/semantics/labPropsScript.sml" \
  "$cake_dir/compiler/backend/semantics"
run_probe word_alloc_setup_colour_probeScript.sml word_alloc_setup_colour_probe.out \
  total_colour_mapped_1 setup0_next "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_alloc_live_colour_noalias_probeScript.sml \
  word_alloc_live_colour_noalias_probe.out \
  colour_ok_distinct_write_live colour_ok_alias_write_live \
  colour_ok_distinct_write_live_after colour_ok_alias_write_live_after \
  "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe apply_colour_probeScript.sml apply_colour_probe.out \
  total_colour_alloc apply_colour_alias_assign apply_colour_alias_const \
  "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
# The legacy allocator-map probe checks the existing WordBijection path too.
run_probe reg_alloc_mk_bij_probeScript.sml reg_alloc_mk_bij_probe.out \
  empty_to seq_next "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe cake_ssa_temp_probeScript.sml cake_ssa_temp_probe.out \
  limit_skip full_skip "$cake_dir/compiler/backend/word_allocScript.sml" \
  "$cake_dir/compiler/backend"
# The reg_alloc probe observes the full IRC colouring (do_reg_alloc via
# reg_alloc_aux/run_ira_state) on tiny clash trees: alloc vars get colours
# 0..k-1, stack-only vars land at >= k, physical vars keep their register
# index.
run_probe reg_alloc_probeScript.sml reg_alloc_probe.out \
  ra_delta_pair moves_to_sp_resort ra_spill_cost \
  node_list_empty_length node_list_first node_list_last \
  node_list_last_in_range node_list_out_of_range \
  node_list_lupdate_same node_list_lupdate_other node_list_lupdate_length \
  node_list_lupdate_outside \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe sort_moves_probeScript.sml sort_moves_probe.out \
  sm_ties_two sm_ties_three sm_desc ra_moves_stemp ra_moves_stemp_hi \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend"
run_probe pan_lang_shape_val_probeScript.sml pan_lang_shape_val_probe.out \
  one named "$cake_dir/pancake/panLangScript.sml"
run_probe shape_to_str_probeScript.sml shape_to_str_probe.out \
  one named "$cake_dir/pancake/panLangScript.sml"
run_probe pan_res_var_probeScript.sml pan_res_var_probe.out \
  delete_hit update_hit "$cake_dir/pancake/semantics/panSemScript.sml"
# The pan_primop probe prints numeric w2n values of the returned RStruct.
run_probe pan_sem_pan_primop_probeScript.sml pan_sem_pan_primop_probe.out \
  pan_primop_basic pan_primop_non_word "$cake_dir/pancake/semantics/panSemScript.sml"
# The set_var probe checks local override, unrelated locals, globals, and clock.
run_probe pan_sem_set_var_probeScript.sml pan_sem_set_var_probe.out \
  set_var_new set_var_done "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_dec_clock_probeScript.sml pan_dec_clock_probe.out \
  pan_dec_clock_five pan_dec_clock_zero \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The dec_clock artifact fixture probe evaluates `tick; return 7` directly.
run_probe pan_sem_dec_clock_e2e_probeScript.sml pan_sem_dec_clock_e2e_probe.out \
  dec_clock_tick_return dec_clock_tick_return_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Tick probe observes both the zero-clock timeout and positive-clock branches.
run_probe pan_sem_tick_e2e_probeScript.sml pan_sem_tick_e2e_probe.out \
  tick_zero_result tick_succ_locals_preserved \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Skip probe observes the normal result with state carried verbatim.
run_probe pan_sem_skip_e2e_probeScript.sml pan_sem_skip_e2e_probe.out \
  skip_result skip_locals_preserved \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_break_continue_e2e_probeScript.sml pan_sem_break_continue_e2e_probe.out \
  break_result continue_locals_preserved \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Assign probe observes the accepted, fresh-destination, and
# source-evaluation-failure branches, including the unchanged post-state on the
# two Error branches.
run_probe pan_sem_assign_e2e_probeScript.sml pan_sem_assign_e2e_probe.out \
  assign_local_ok_result assign_eval_missing_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Dec probe observes the accepted declaration with local restoration, the
# shape-mismatch rejection, and the initialiser-evaluation-failure rejection,
# including the unchanged post-state of both rejection branches.
# The Primitive-error probe observes `pan_primop` failure (wrong arity) and a
# destination shape mismatch, both yielding `SOME Error` with unchanged state.
run_probe pan_sem_primitive_error_probeScript.sml pan_sem_primitive_error_probe.out \
  prim_wrong_arity_result prim_shape_mismatch_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"

run_probe pan_sem_dec_e2e_probeScript.sml pan_sem_dec_e2e_probe.out \
  dec_ok_result dec_eval_missing_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Primitive probe observes the accepted AddCarry update, the
# fresh-destination rejection, and the argument-evaluation-failure rejection,
# including the unchanged post-state of both rejection branches.
run_probe pan_sem_primitive_e2e_probeScript.sml pan_sem_primitive_e2e_probe.out \
  prim_ok_result prim_arg_missing_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Error-propagation probe nests a rejected Dec inside Seq and While and
# observes that the explicit `SOME Error` result propagates.
run_probe pan_sem_error_prop_e2e_probeScript.sml pan_sem_error_prop_e2e_probe.out \
  seq_error_result while_error_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Store/ShMem/If probe observes successful execution and the explicit
# `SOME Error` results with unchanged state for the store, shared-memory, and
# condition rejection branches.
run_probe pan_sem_store_error_probeScript.sml pan_sem_store_error_probe.out \
  if_ok_result shmemstore_domain_result \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The While probe observes the explicit `SOME Error` for a non-word condition,
# the same-clock normal exit for a zero condition, clock-exhaustion timeout,
# and a one-iteration exit that clears the condition.
run_probe pan_sem_while_error_probeScript.sml pan_sem_while_error_probe.out \
  while_bad_result while_one_iter_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Seq probe observes the normal continuation, the `Break`/`Continue`
# short-circuit (second command not run), the rejected first command, and the
# `fix_clock` clamp after a `Tick`.
run_probe pan_sem_seq_e2e_probeScript.sml pan_sem_seq_e2e_probe.out \
  seq_normal_result seq_tick_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The If probe observes the then/else branches, non-word and failed conditions,
# plus Const, Var Local, and operator-expression branch selection in the
# restricted total evaluators.
run_probe pan_sem_ite_e2e_probeScript.sml pan_sem_ite_e2e_probe.out \
  if_true_result exact_if_failed_local \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The measure-driven total fragment probe observes Assign/Return/Raise result
# and state branches, plus their interaction with If selection and Seq stopping.
run_probe pan_sem_total_fragment_stmt_probeScript.sml pan_sem_total_fragment_stmt_probe.out \
  total_assign_ok_result total_assign_ok_local \
  total_assign_bad_result total_assign_bad_local \
  total_return_ok_result total_return_ok_local \
  total_return_bad_result total_return_bad_local \
  total_return_oversize_result total_return_oversize_local \
  total_raise_ok_result total_raise_ok_local \
  total_raise_bad_result total_raise_bad_local \
  total_raise_shape_mismatch_result total_raise_shape_mismatch_local \
  total_raise_missing_shape_result total_raise_oversize_result \
  total_raise_oversize_local total_if_assign_true_result \
  total_if_assign_true_local total_if_assign_false_result \
  total_if_assign_false_local total_seq_assign_return_result \
  total_seq_assign_return_local total_seq_raise_stop_result \
  total_seq_raise_stop_local \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The If memory probe observes a memory-reading condition: a nonzero cell
# selecting the then branch, a zero cell selecting the else branch, an address
# outside `memaddrs` rejected with Error, and the same cell selecting different
# branches under little- versus big-endian byte reads.
run_probe pan_sem_ite_memory_probeScript.sml pan_sem_ite_memory_probe.out \
  if_mem_nonzero_result if_mem_byte_be_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Assign memory probe observes a memory-reading source: a present word cell
# written to the destination local, an address outside `memaddrs` rejected with
# Error and the locals/clock unchanged, and `be` driving the byte read.
run_probe pan_sem_assign_memory_probeScript.sml pan_sem_assign_memory_probe.out \
  assign_mem_load_result assign_mem_byte_be_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The DecCall probe observes the successful continuation, the wrong-shape
# rejection, the failing-callee rejection, and the unknown-function rejection.
run_probe pan_sem_deccall_error_probeScript.sml pan_sem_deccall_error_probe.out \
  deccall_ok_result nested_deccall_bad_shape_state_exact \
  "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The Call argument probe observes that a failing argument rejects the call
# with `SOME Error` before callee lookup, preserving clock and locals.
run_probe pan_sem_call_arg_error_probeScript.sml pan_sem_call_arg_error_probe.out \
  call_arg_fail_result call_arg_fail_missing_result \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call error-state probe observes that a memory-reading argument is gated by
# the source `memaddrs` (an address outside the domain rejects the call even
# when the raw memory function holds a cell), and that an unknown callee is
# rejected, both with `SOME Error` and the unchanged state.
run_probe pan_sem_call_error_state_probeScript.sml pan_sem_call_error_state_probe.out \
  call_error_load_result call_error_missing_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call arity probe observes that a parameter-shape/arity mismatch rejects the
# call with `SOME Error` and the unchanged caller state, while a matching
# argument yields the callee's `Return` result.
run_probe pan_sem_call_arity_probeScript.sml pan_sem_call_arity_probe.out \
  call_arity_miss_result call_arity_shape_miss_result \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call callee-fallthrough probe observes that a callee whose body terminates
# normally (HOL `NONE`) rejects the call with `SOME Error`, preserving the
# callee's bound parameter locals and the decremented clock.
run_probe pan_sem_call_callee_normal_probeScript.sml pan_sem_call_callee_normal_probe.out \
  call_normal_result call_normal_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call callee-terminal probe observes that a callee whose body finishes with
# `Break` or `Continue` rejects the call with `SOME Error`, preserving the
# callee's bound parameter locals and the decremented clock.
run_probe pan_sem_call_callee_terminal_probeScript.sml pan_sem_call_callee_terminal_probe.out \
  call_break_result call_continue_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call callee-error probe observes that a callee whose body finishes with
# `SOME Error` propagates `SOME Error` through the catch-all `empty_locals st`,
# clearing the caller-visible locals while keeping the decremented clock.
run_probe pan_sem_call_callee_error_probeScript.sml pan_sem_call_callee_error_probe.out \
  call_error_result call_error_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Call return-invalid probe observes that a callee returning a value whose
# shape does not match the declared return shape rejects the call with
# `SOME Error` at the decremented callee clock.
run_probe pan_sem_call_return_invalid_probeScript.sml pan_sem_call_return_invalid_probe.out \
  call_retinvalid_result call_retinvalid_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Return/Raise probe observes evaluation failure and shape/size rejection
# with `SOME Error` and the unchanged state, plus the successful results with
# cleared locals.
run_probe pan_sem_return_raise_error_probeScript.sml pan_sem_return_raise_error_probe.out \
  ret_eval_fail_result raise_ok_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The Return/Raise memory probe observes a memory-reading payload: a domain
# miss rejected with Error and unchanged state for both `Return` and `Raise`, a
# shape mismatch rejected with unchanged state, and the successful
# memory-reading results with cleared locals.
run_probe pan_sem_return_raise_memory_probeScript.sml pan_sem_return_raise_memory_probe.out \
  ret_mem_fail_result raise_mem_ok_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
# The ExtCall error probe observes the argument-evaluation failure, the
# non-word argument and failing byte-read rejections, each returning
# `SOME Error` with unchanged state.
run_probe pan_sem_extcall_error_probeScript.sml pan_sem_extcall_error_probe.out \
  ext_nonword_result ext_argfail_done \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_call_terminal_probeScript.sml pan_sem_call_terminal_probe.out \
  call_terminal_skip_result call_terminal_continue_param_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_fix_clock_probeScript.sml pan_fix_clock_probe.out \
  pan_fix_clock_clamps pan_fix_clock_keeps_lower \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_upd_locals_probeScript.sml pan_upd_locals_probe.out \
  pan_upd_locals_hit pan_upd_locals_empty \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_lookup_code_probeScript.sml pan_sem_lookup_code_probe.out \
  lookup_code_nonempty_success lookup_code_wf_shape_invariant_step_success \
  lookup_code_missing_function \
  lookup_code_wrong_arity lookup_code_wrong_shape lookup_code_duplicate_formals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_e2e_probeScript.sml pan_sem_e2e_probe.out \
  return_41 call_code_map_7 recursive_call_code_map_7 deccall_code_map_7 \
  recursive_call_timeout recursive_deccall_timeout pan_sem_e2e_done \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe crep_clock_leaf_eval_probeScript.sml crep_clock_leaf_eval_probe.out \
  skip_eval break_eval continue_eval tick_zero_eval tick_positive_eval \
  if_true_eval if_false_eval if_error_eval if_nested_eval \
  seq_skip_break_eval seq_break_stops_eval seq_tick_skip_eval seq_tick_zero_eval \
  seq_fix_clock_upper_clamp_eval return_word_eval return_empty_eval \
  return_missing_eval raise_eval dec_shadow_eval dec_new_local_eval dec_error_eval \
  while_false_eval while_error_eval while_timeout_eval while_normal_recursion_eval \
  while_break_zero_eval while_break_label_eval while_continue_label_eval \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_total_call_eval_probeScript.sml crep_total_call_eval_probe.out \
  call_total_return_success call_total_return_destination call_total_missing_code \
  call_total_wrong_arity call_total_timeout call_total_callee_normal \
  call_total_callee_break call_total_callee_continue call_total_callee_exception \
  call_total_return_arity_error call_total_duplicate_destinations \
  call_total_missing_destination \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_assign_eval_probeScript.sml crep_assign_eval_probe.out \
  assign_overwrite_eval assign_missing_destination_eval assign_expression_error_eval \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_store_eval_probeScript.sml crep_store_eval_probe.out \
  store_success store_address_error store_value_error store_domain_error \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_ext_call_eval_probeScript.sml crep_ext_call_eval_probe.out \
  extcall_return_eval extcall_final_eval extcall_missing_local_eval \
  extcall_read_error_eval \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_shmem_eval_probeScript.sml crep_shmem_eval_probe.out \
  shmem_load_success shmem_store_success shmem_load8_success shmem_store8_success \
  shmem_load_domain_error \
  shmem_missing_local_error shmem_load_final \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe pan_sem_call_return_shape_probeScript.sml pan_sem_call_return_shape_probe.out \
  call_good_return_shape_result call_bad_return_shape_result call_bad_return_shape_param_local \
  "$cake_dir/pancake/semantics/panSemScript.sml"
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
run_probe ffi_call_probeScript.sml ffi_call_probe.out \
  oracle_return extcall_name_len "$cake_dir/semantics/ffi/ffiScript.sml"
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
run_probe pan_sem_set_global_probeScript.sml pan_sem_set_global_probe.out \
  set_global_insert set_global_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_set_kvar_probeScript.sml pan_sem_set_kvar_probe.out \
  set_kvar_local set_kvar_global_locals \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_lookup_kvar_probeScript.sml pan_sem_lookup_kvar_probe.out \
  lookup_kvar_local lookup_kvar_missing \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_is_valid_value_probeScript.sml pan_sem_is_valid_value_probe.out \
  is_valid_value_local_shape is_valid_value_missing \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_write_bytearray_probeScript.sml pan_sem_write_bytearray_probe.out \
  write_empty write_miss \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_mem_store_byte_probeScript.sml pan_sem_mem_store_byte_probe.out \
  store_byte_hit_some write_bytearray_out_of_domain \
  "$cake_dir/pancake/semantics/panSemScript.sml" "$cake_dir/pancake/semantics"
run_probe pan_sem_evaluate_fixed_load_probeScript.sml \
  pan_sem_evaluate_fixed_load_probe.out \
  eval_byte_hit eval_load32_alignment_failure \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sem_evaluate_fixed_store_probeScript.sml \
  pan_sem_evaluate_fixed_store_probe.out \
  evaluate_store_word_hit evaluate_store_byte_domain_failure \
  "$cake_dir/pancake/semantics/panSemScript.sml"
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
run_probe pan_nb_op_probeScript.sml pan_nb_op_probe.out \
  op8 op32 \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sh_mem_load_probeScript.sml pan_sh_mem_load_probe.out \
  zero_width_domain_error nonzero_width_domain_error \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_sh_mem_store_probeScript.sml pan_sh_mem_store_probe.out \
  zero_width_domain_error nonzero_width_domain_error \
  "$cake_dir/pancake/semantics/panSemScript.sml"
run_probe pan_eval_probeScript.sml pan_eval_probe.out \
  eval_const eval_probe_done \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_mrec_probeScript.sml pan_mrec_probe.out \
  mrec_ret mrec_external \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_h_prog_call_probeScript.sml \
  pan_itree_h_prog_call_probe.out \
  call_eval_failure call_success \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_bst_probeScript.sml pan_bst_probe.out \
  bst_locals bst_clock_ffi_irrelevant \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_set_var_probeScript.sml pan_itree_set_var_probe.out \
  set_var_new set_var_globals \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe pan_itree_empty_locals_probeScript.sml pan_itree_empty_locals_probe.out \
  empty_locals_local empty_locals_base_addr \
  "$cake_dir/pancake/semantics/pan_itreeSemScript.sml"
run_probe crep_primop_probeScript.sml crep_primop_probe.out \
  crep_basic crep_wrong_length \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_load_shape_probeScript.sml crep_load_shape_probe.out \
  empty nonzero_two "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_load_shape64_probeScript.sml crep_load_shape64_probe.out \
  empty64 nonzero_two64 "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_to_loop_cutset_probeScript.sml crep_to_loop_cutset_probe.out \
  cut_set_const_args handler_original_live "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe crep_nested_seq_probeScript.sml crep_nested_seq_probe.out \
  empty assign_seq "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_assigned_free_vars_probeScript.sml crep_assigned_free_vars_probe.out \
  skip shmem_fallback "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_stores_probeScript.sml crep_stores_probe.out \
  empty nonzero_two "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_nested_decs_probeScript.sml crep_nested_decs_probe.out \
  empty values_empty "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_store_globals_probeScript.sml crep_store_globals_probe.out \
  empty two "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_load_globals_probeScript.sml crep_load_globals_probe.out \
  empty three "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_assign_ret_probeScript.sml crep_assign_ret_probe.out \
  empty two "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_var_cexp_probeScript.sml crep_var_cexp_probe.out \
  const base_top "$cake_dir/pancake/crepLangScript.sml"
run_probe crep_exps_probeScript.sml crep_exps_probe.out \
  leaves loads ops "$cake_dir/pancake/crepLangScript.sml"
run_probe cexp_heads_probeScript.sml cexp_heads_probe.out \
  empty heads empty_head empty_tail inferred_type "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe comp_field_probeScript.sml comp_field_probe.out \
  first short "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe compile_panop_probeScript.sml compile_panop_probe.out \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe compile_exp_probeScript.sml compile_exp_probe.out \
  leaves bytes_in_word nstruct nfield load_one load_two struct_field loads_ops cmp_shift finite_map_shadow finite_map_load32_local \
  finite_map_load_byte_local loadbyte_recursive_address \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe exp_hdl_probeScript.sml exp_hdl_probe.out \
  missing known dup_update dup_list "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe ret_var_probeScript.sml ret_var_probe.out \
  one_empty named "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe ret_hdl_probeScript.sml ret_hdl_probe.out \
  one named "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe wrap_rt_probeScript.sml wrap_rt_probe.out \
  none named "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe compile_def_probeScript.sml compile_def_probe.out \
  return missing_global empty_one_global extra_names_global missing_names_global \
  missing_local empty_one_local extra_names_local missing_names_local valid_local \
  empty_struct_return finite_map_shadow_return extcall_high_tail \
  extcall_shared_high_tail \
  pair_load pair_store fixed_stride64 \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe compile_to_crep_probeScript.sml compile_to_crep_probe.out \
  empty raise_const raise_pair raise_pair_later raise_pair_later_64 handled_pair done \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe crep_alookup_compile_probeScript.sml crep_alookup_compile_probe.out \
  source_names_distinct alookup_param_entry "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe crep_el_compile_probeScript.sml crep_el_compile_probe.out \
  source_el_f compiled_el_f "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe crep_make_funcs_probeScript.sml crep_make_funcs_probe.out \
  make_funcs_empty_params make_funcs_duplicate_first_wins "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe crep_get_eids_probeScript.sml crep_get_eids_probe.out \
  eids_present eids_codes_distinct "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe crep_vmap_ctxtfc_probeScript.sml crep_vmap_ctxtfc_probe.out \
  vmap_x vmap_eq_ctxt "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe dup_exn_eids_probeScript.sml dup_exn_eids_probe.out \
  dup_eids_lookup mixed_eids_lookup_a mixed_eids_lookup_e dup_compile done \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe compile_prog_probeScript.sml compile_prog_probe.out \
  empty inline_call global_dest handled_missing_dest done \
  "$cake_dir/pancake/pan_to_crepScript.sml"
run_probe excp_rel_probeScript.sml excp_rel_probe.out \
  empty_maps noninjective_compiler_codes \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe ctxt_fc_probeScript.sml ctxt_fc_probe.out \
  shaped_slots empty_maximum functions_projection vmax_nonempty_list vmax_empty_list \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe code_rel_probeScript.sml code_rel_probe.out \
  code_rel_type compiled_return localised_return localised_global_assignment \
  function_signature_lookup target_function_lookup code_rel_rejects_unlocalised_source \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe globals_lookup_probeScript.sml globals_lookup_probe.out \
  lookup_success lookup_missing lookup_struct \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"
run_probe pan_globals_compile_top_probeScript.sml pan_globals_compile_top_probe.out \
  missing_start global_present present_start "$cake_dir/pancake/pan_globalsScript.sml"
run_probe pan_globals_compile_decs_probeScript.sml pan_globals_compile_decs_probe.out \
  empty compile_decs_probe_done "$cake_dir/pancake/pan_globalsScript.sml"
run_probe smart_seq_probeScript.sml smart_seq_probe.out \
  skip_skip skip_tick tick_skip tick_tick "$cake_dir/pancake/pan_simpScript.sml"
run_probe seq_assoc_probeScript.sml seq_assoc_probe.out \
  skip_skip tick_skip tick_seq_skip_tick tick_return \
  "$cake_dir/pancake/pan_simpScript.sml"
run_probe seq_call_ret_probeScript.sml seq_call_ret_probe.out \
  matching_return mismatching_return fallback \
  "$cake_dir/pancake/pan_simpScript.sml"
run_probe ret_to_tail_probeScript.sml ret_to_tail_probe.out \
  skip tail_call mismatching_return handler_seq \
  "$cake_dir/pancake/pan_simpScript.sml"
run_probe pan_simp_compile_probeScript.sml pan_simp_compile_probe.out \
  skip seq_skip_tick tail_call "$cake_dir/pancake/pan_simpScript.sml"
run_probe crep_exit_loop_probeScript.sml crep_exit_loop_probe.out \
  exit_loop_break exit_loop_error \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_evaluate_probeScript.sml crep_evaluate_probe.out \
  evaluate_skip evaluate_tick_timeout \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_fix_clock_probeScript.sml crep_fix_clock_probe.out \
  fix_clock_clamps fix_clock_keeps_lower \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_local_updates_probeScript.sml crep_local_updates_probe.out \
  set_var_hit empty_locals_fields_preserved \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_sh_mem_load_probeScript.sml crep_sh_mem_load_probe.out \
  sh_mem_load_zero_width_domain_error sh_mem_load_nonzero_domain_error \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_sh_mem_op_probeScript.sml crep_sh_mem_op_probe.out \
  sh_mem_op_load sh_mem_op_store \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_sh_mem_store_probeScript.sml crep_sh_mem_store_probe.out \
  sh_mem_store_missing_local sh_mem_store_nonzero_domain_error \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_mem_load_probeScript.sml crep_mem_load_probe.out \
  mem_load_hit mem_load_miss \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_op_probeScript.sml crep_op_probe.out \
  op_mul_two op_mul_empty \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_eval_probeScript.sml crep_eval_probe.out \
  eval_const eval_base_top \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_dest_2exp_probeScript.sml crep_dest_2exp_probe.out \
  zero highest_shift_conclusion bound_eight \
  "$cake_dir/pancake/crep_arithScript.sml"
run_probe hol_fcp_index_n2w_probeScript.sml hol_fcp_index_n2w_probe.out \
  n2w_zero_word bit_high6 "$hol_dir/src/n-bit/wordsScript.sml" \
  "$hol_dir/src/n-bit"
run_probe hol_word_arithmetic_probeScript.sml hol_word_arithmetic_probe.out \
  word_add_definition sub_3_5_8 "$hol_dir/src/n-bit/wordsScript.sml" \
  "$hol_dir/src/n-bit"
run_probe word_op_finite_probeScript.sml word_op_finite_probe.out \
  word_op_definition word_op_finite_done \
  "$cake_dir/compiler/backend/wordLangScript.sml" \
  "$cake_dir/compiler/backend"
run_probe word_sh_finite_probeScript.sml word_sh_finite_probe.out \
  word_sh_definition lsl_above_width \
  "$cake_dir/compiler/backend/wordLangScript.sml" \
  "$cake_dir/compiler/backend"
run_probe crep_mul_const_probeScript.sml crep_mul_const_probe.out \
  zero eight "$cake_dir/pancake/crep_arithScript.sml"
run_probe crep_simp_exp_probeScript.sml crep_simp_exp_probe.out \
  const_mul eval_simp_after "$cake_dir/pancake/crep_arithScript.sml"
run_probe crep_simp_prog_probeScript.sml crep_simp_prog_probe.out \
  assign unchanged "$cake_dir/pancake/crep_arithScript.sml"
run_probe afindi_probeScript.sml afindi_probe.out \
  empty duplicate_first wf_shape_drop dropWhile_MAP_helper UNCURRY_EQ_o_SND_pair \
  map_uncurry_zip_again struct_infos_ok_drop struct_infos_ok_append \
  struct_infos_ok_cons alookup_map_structs_ok fields_in_order_reorder_noop \
  opt_mmap_eq_every alookup_drop_helper map_fst_eq_alookup \
  map_fst_eq_alookup_different_value_types map_fst_eq_alookup_inferred_types \
  "$cake_dir/pancake/proofs/pan_structsProofScript.sml"
run_probe pan_structs_compile_exp_probeScript.sml pan_structs_compile_exp_probe.out \
  rstruct old_shapes_map "$cake_dir/pancake/pan_structsScript.sml"
run_probe crep_semantics_probeScript.sml crep_semantics_probe.out \
  semantics_timeout_is_nonterminal semantics_break_is_nonterminal \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_res_var_probeScript.sml crep_res_var_probe.out \
  res_var_delete_hit res_var_update_hit \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
run_probe crep_lookup_code_probeScript.sml crep_lookup_code_probe.out \
  lookup_code_valid lookup_code_duplicate \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
# The store_global probe observes StoreGlob insert/update/error on globals.
run_probe crep_store_global_probeScript.sml crep_store_global_probe.out \
  set_globals_direct store_global_then_load \
  "$cake_dir/pancake/semantics/crepSemScript.sml"
# The locals_wordlab probe observes varname |-> word_lab cell retention,
# Var-read flattening and overwrite behaviour.
run_probe crep_locals_wordlab_probeScript.sml crep_locals_wordlab_probe.out \
  locals_set_var_cell locals_set_var_overwrite \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_replicate_const_probeScript.sml crep_replicate_const_probe.out \
  replicate_const_one replicate_const_nonzero \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The mem_load probe observes the total word -> word_lab memory function and the
# memaddrs guard on both mem_load and eval (Load ...).
run_probe crep_mem_load_probeScript.sml crep_mem_load_probe.out \
  mem_load_valid eval_load_invalid \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe crep_mem_store_probeScript.sml crep_mem_store_probe.out \
  mem_store_valid_lookup mem_store_invalid \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval LoadByte probe observes the fixed RV64 get_byte/byte_align path:
# little-endian byte extraction from a total word -> word_lab memory, plus the
# memaddrs guard and the underlying mem_load_byte.
run_probe crep_eval_load_byte_probeScript.sml crep_eval_load_byte_probe.out \
  eval_loadbyte_addr8 eval_loadbyte_w24_be_addr5 \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Load32 probe observes the fixed RV64 aligned four-byte read:
# little-endian and big-endian byte order, alignment failure, and the memaddrs
# domain failure over a total word -> word_lab memory.
run_probe crep_eval_load_32_probeScript.sml crep_eval_load_32_probe.out \
  eval_load32_le_addr8 eval_load32_w24_addr4 \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Load (word cell) probe observes the fixed RV64 total word -> word_lab
# memory cell read: a live cell and the memaddrs domain failure.
run_probe crep_eval_load_rv64_probeScript.sml crep_eval_load_rv64_probe.out \
  mem_load_valid eval_load_outside_domain \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval StoreByte probe observes HOL set_byte at a nonzero byte offset: the
# cell updated at address 8 and at address 9, plus the memaddrs domain failure.
run_probe crep_eval_store_byte_offset_probeScript.sml \
  crep_eval_store_byte_offset_probe.out \
  storebyte_offset9_result storebyte_outside_domain_mem8 \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Store32 high-bits probe observes HOL `mem_store_32`'s up-front `w2w`
# truncation: storing 0xDEADBEEF11223344 and 0x11223344 leave the same cell.
run_probe crep_eval_store_32_highbits_probeScript.sml \
  crep_eval_store_32_highbits_probe.out \
  w2w_highbits store32_unaligned_result \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Op probe observes HOL word_op folding over constant operands for the
# RV64 target (Add/Sub/And, plus the empty-Add neutral and the Sub arity failure).
run_probe crep_eval_op_rv64_probeScript.sml crep_eval_op_rv64_probe.out \
  eval_op_add_const eval_op_sub_arity \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Cmp probe observes HOL word_cmp over constant operands for the RV64
# target (Equal/Lower/Test true and false).
run_probe crep_eval_cmp_rv64_probeScript.sml crep_eval_cmp_rv64_probe.out \
  eval_cmp_equal_true eval_cmp_not_test_overlap \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The eval Shift probe observes HOL word_sh over constant operands for the RV64
# target (Lsl/Lsr/Asr/Ror, amount zero, and the invalid width-sized amount).
run_probe crep_eval_shift_rv64_probeScript.sml crep_eval_shift_rv64_probe.out \
  eval_shift_lsl_const eval_shift_amount_width \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
# The Crepop Mul probe observes HOL crep_op over constant operands (product and
# the arity failures for three, one, and zero operands).
run_probe crep_eval_crepop_mul_rv64_probeScript.sml crep_eval_crepop_mul_rv64_probe.out \
  eval_crepop_mul_const eval_crepop_mul_empty \
  "$cake_dir/pancake/semantics/crepSemScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe prog_if_probeScript.sml prog_if_probe.out \
  prog_if_basic prog_if_basic \
  "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe compile_crepop_probeScript.sml compile_crepop_probe.out \
  compile_crepop_mul_riscv compile_crepop_mul_riscv \
  "$cake_dir/pancake/crep_to_loopScript.sml"
run_probe pan_empty_locals_probeScript.sml pan_empty_locals_probe.out \
  empty_locals empty_locals_clock \
  "$cake_dir/pancake/semantics/panSemScript.sml"
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
run_probe loop_props_get_vars_probeScript.sml \
  loop_props_get_vars_probe.out \
  get_vars_two get_var_imm_add_clk_eq \
  "$cake_dir/pancake/semantics/loopPropsScript.sml" \
  "$cake_dir/pancake/semantics"
run_probe loop_sem_call_env_probeScript.sml \
  loop_sem_call_env_probe.out \
  arg_zero arg_missing "$cake_dir/pancake/semantics/loopSemScript.sml"
# The locals_touched probe observes the structural Loop expression analysis.
run_probe loop_lang_locals_touched_probeScript.sml \
  loop_lang_locals_touched_probe.out \
  const base_addr "$cake_dir/pancake/loopLangScript.sml"
run_probe vars_of_exp_probeScript.sml vars_of_exp_probe.out \
  var shift_nested "$cake_dir/pancake/loop_liveScript.sml"
run_probe arith_vars_probeScript.sml arith_vars_probe.out \
  long_mul long_div "$cake_dir/pancake/loop_liveScript.sml"
run_probe shrink_leaf_probeScript.sml shrink_leaf_probe.out \
  skip load32 "$cake_dir/pancake/loop_liveScript.sml"
run_probe mark_all_probeScript.sml mark_all_probe.out \
  seq_mark call_handler "$cake_dir/pancake/loop_liveScript.sml"
run_probe loop_live_comp_probeScript.sml loop_live_comp_probe.out \
  skip return "$cake_dir/pancake/loop_liveScript.sml"
run_probe ocompile_probeScript.sml ocompile_probe.out \
  skip post_return_skip "$cake_dir/pancake/crep_to_loopScript.sml"
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
run_probe loop_sem_ffi_probeScript.sml loop_sem_ffi_probe.out \
  extcall_returned extcall_missing_local \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe loop_sem_ffi_rv64_probeScript.sml loop_sem_ffi_rv64_probe.out \
  rv64_lookups rv64_extcall_live_absent \
  "$cake_dir/pancake/semantics/loopSemScript.sml"
run_probe byte_align_probeScript.sml byte_align_probe.out \
  ba24_5 ba8_7 "$cake_dir/pancake/semantics/loopSemScript.sml"
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
run_probe word_byte_memory_probeScript.sml word_byte_memory_probe.out \
  byte_index_definition set_byte_width17_big_nonzero_numeric \
  "$hol_dir/src/n-bit/byteScript.sml" "$hol_dir/src/n-bit"
# `labels_rel` is the wordConvs label-preservation relation; the fixture
# simplifies under `labels_rel_def` because `EVAL` leaves `set ... SUBSET ...`.
run_probe word_convs_labels_rel_probeScript.sml word_convs_labels_rel_probe.out \
  labels_rel_refl_ok labels_rel_pair_ok \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"
# `extract_labels` collects the Call handler label pairs (and descends into
# return/handler/Seq/Loop/If bodies); with no Call return metadata it is empty
# even when a handler is present.
run_probe word_convs_extract_labels_probeScript.sml word_convs_extract_labels_probe.out \
  el_inst el_nested \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The instruction-predicate probe observes the `distinct_tar_reg` and
# `two_reg_inst` arithmetic cases, and `every_inst` descending through the
# program's structural positions (including the `Call` return-metadata
# nesting).
run_probe word_convs_inst_preds_probeScript.sml word_convs_inst_preds_probe.out \
  dtr_binop_same ei_alloc \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The flat-exp probe observes the expression-shape restrictions of
# `flat_exp_conventions` and its descent through composition and `Call`.
run_probe word_convs_flat_exp_probeScript.sml word_convs_flat_exp_probe.out \
  fl_assign fl_inst \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The asm_config probe observes each HOL assembler validity predicate and
# configuration projection used by `stackProps$stack_asm_ok`, plus `asm_ok`
# over the full `asm` datatype (Inst/Jump/JumpCmp/Call/JumpReg/Loc).
run_probe asm_config_checks_probeScript.sml asm_config_checks_probe.out \
  aligned0 asmOkLoc \
  "$cake_dir/compiler/backend/semantics/stackPropsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# Direct HOL fixture for wordConvs$inst_ok_less, the weaker per-instruction
# well-formedness predicate consumed by compile_to_word_conventions2.
run_probe word_convs_inst_ok_less_probeScript.sml word_convs_inst_ok_less_probe.out \
  iol_binop_imm iol_movfromreg_fp_out_of_range \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The full_inst_ok_less probe observes `exp_to_addr` and the lifted
# `wordConvs$full_inst_ok_less` predicate over the backend wordLang syntax.
run_probe word_convs_full_inst_ok_less_probeScript.sml word_convs_full_inst_ok_less_probe.out \
  eta_var fiol_alloc \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The call_arg_convention probe observes `wordConvs$inst_arg_convention` and
# `wordConvs$call_arg_convention` over the backend wordLang syntax.
run_probe word_convs_call_arg_probeScript.sml word_convs_call_arg_probe.out \
  inst_addcarry_ok call_seq_bad \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The register-allocation partition probe observes the three predicates and
# the partition lemma on representative residues.
run_probe reg_alloc_var_partition_probeScript.sml reg_alloc_var_partition_probe.out \
  is_phy_6 part_none_0 \
  "$cake_dir/compiler/backend/reg_alloc/reg_allocScript.sml" \
  "$cake_dir/compiler/backend/reg_alloc"

# The not-created-subprograms probe observes the four no_* specialisations on
# their own constants and on nesting/handler cases.
run_probe word_convs_not_created_probeScript.sml word_convs_not_created_probe.out \
  nac_skip nac_install_empty \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The every_var family probe observes the wordLang expression/immediate/
# instruction revisors on even/odd registers and the width-dependent FP moves.
run_probe word_lang_every_var_probeScript.sml word_lang_every_var_probe.out \
  evar_var einst_skip \
  "$cake_dir/compiler/backend/wordLangScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The good_handlers probe observes the structural handler-label predicate,
# including the NONE-ret case (handler ignored) and nested bad handlers.
run_probe word_convs_good_handlers_probeScript.sml word_convs_good_handlers_probe.out \
  gh_call_none gh_other \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The num_set audit probe observes HOL misc$num_set = unit spt behaviour via
# sptree$toAList: canonical insertion-order-independent enumeration, duplicate
# collapse, wf for LN/insert/union, order-insensitive EVERY, and left-bias of
# union / last-write of insert for non-unit maps.
run_probe num_set_audit_probeScript.sml num_set_audit_probe.out \
  ns_empty nsmap_insert_last \
  "$cake_dir/misc/miscScript.sml" \
  "$cake_dir/misc"

# Every name/var/stack-var predicates (num_set domain model): the probe also
# shows every_stack_var ignores the scalar FFI registers (only every_name / body).
run_probe word_lang_every_name_probeScript.sml word_lang_every_name_probe.out \
  en_empty esv_seq_bad \
  "$cake_dir/compiler/backend/wordLangScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# `pre_alloc_conventions` / `post_alloc_conventions`: stack/phy predicates,
# the `2*k` bound, and the call-argument convention.
run_probe word_convs_alloc_conventions_probeScript.sml word_convs_alloc_conventions_probe.out \
  pre_ok_ffi post_ok_ret \
  "$cake_dir/compiler/backend/semantics/wordConvsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The labProps probe pins `line_ok_pre`/`all_enc_ok_pre` and the concrete
# `cbw_to_asm` mapping at an 8-bit configuration.
run_probe lab_props_line_ok_pre_probeScript.sml lab_props_line_ok_pre_probe.out \
  line_ok_asm_skip all_enc_ok_empty \
  "$cake_dir/compiler/backend/semantics/labPropsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The stack_to_lab flatten-ops probe observes the config-independent embedded
# constructors (negate table and compile_jump).
run_probe stack_to_lab_flatten_ops_probeScript.sml stack_to_lab_flatten_ops_probe.out \
  negate_less compile_jump_reg \
  "$cake_dir/compiler/backend/stack_to_labScript.sml" \
  "$cake_dir/compiler/backend"

# The flatten base probe observes the non-recursive flatten constructors.
run_probe stack_to_lab_flatten_base_probeScript.sml stack_to_lab_flatten_base_probe.out \
  flatten_tick flatten_halt \
  "$cake_dir/compiler/backend/stack_to_labScript.sml" \
  "$cake_dir/compiler/backend"

# The RISC-V configuration probe observes the exact `riscv_config` field
# values at 64-bit (register file, offsets, immediates) used by the stack
# assembler checks.
run_probe riscv_config_probeScript.sml riscv_config_probe.out \
  cfg_isa valid_imm_add_max12p1 \
  "$cake_dir/compiler/encoders/riscv/riscv_targetScript.sml" \
  "$cake_dir/compiler/encoders/riscv"

# The misc app_list probe observes HOL `append_aux`/`append` flattening the
# `app_list` concatenation tree used by the stack_to_lab flatten statement.
run_probe misc_app_list_probeScript.sml misc_app_list_probe.out \
  append_aux_list append_aux_suffix \
  "$cake_dir/misc/miscScript.sml" \
  "$cake_dir/misc"

# The flatten app_list probe observes `misc$append` flattening the HOL
# `stack_to_lab$flatten` app_list output to the production flat list.
run_probe stack_to_lab_flatten_app_list_probeScript.sml stack_to_lab_flatten_app_list_probe.out \
  flatten_app_tick flatten_app_ite_tick \
  "$cake_dir/compiler/backend/stack_to_labScript.sml" \
  "$cake_dir/compiler/backend"

# The labProps sec_ends_with_label probe observes the `is_Label` classifier and
# the `¬NULL ls ∧ is_Label (LAST ls)` section test used by
# `EVERY_sec_ends_with_label_MAP_prog_to_section`.
run_probe lab_props_sec_ends_label_probeScript.sml lab_props_sec_ends_label_probe.out \
  is_label_label sec_empty \
  "$cake_dir/compiler/backend/semantics/labPropsScript.sml" \
  "$cake_dir/compiler/backend/semantics"

# The stack_names probe observes the pure register-renaming transformation
# (ri_find_name / inst_find_name / dest_find_name / comp / prog_comp /
# compile / names_ok) against a small renaming map.
run_probe stack_names_ports_probeScript.sml stack_names_ports_probe.out \
  ri_reg compile_map_fst_src \
  "$cake_dir/compiler/backend/stack_namesScript.sml" \
  "$cake_dir/compiler/backend"

# The stack_remove make_init probe observes the state-free prerequisites used by
# init_reduce / init_prop: is_SOME_Word, read_mem (and its LENGTH) and the
# addresses set with its membership characterization.
run_probe stack_remove_init_probeScript.sml stack_remove_init_probe.out \
  is_word_some in_addr_out \
  "$cake_dir/compiler/backend/proofs/stack_removeProofScript.sml" \
  "$cake_dir/compiler/backend/proofs"

# The word_loc probe pins the exact width-indexed HOL stackLang word_loc
# datatype (Word ('a word) | Loc num num) used by StackRemove.
run_probe word_lang_word_loc_probeScript.sml word_lang_word_loc_probe.out \
  wl_word wl_match \
  "$cake_dir/compiler/backend/wordLangScript.sml" \
  "$cake_dir/compiler/backend"

# The stack_remove value-helper probe pins max_stack_alloc, word_offset (8/64),
# store_list (length/head/last), store_length and stack_err_lab from the
# stack_remove compiler script.
run_probe stack_remove_helpers_probeScript.sml stack_remove_helpers_probe.out \
  max_stack_alloc stack_err_lab \
  "$cake_dir/compiler/backend/stack_removeScript.sml" \
  "$cake_dir/compiler/backend"

# The stackLang instruction-overload probe pins left_shift_inst,
# right_shift_inst, const_inst, load_inst, store_inst (stackLangScript.sml:80-84)
# and halt_inst (stack_removeScript.sml:58) against explicit constructor terms.
run_probe stack_lang_inst_overloads_probeScript.sml stack_lang_inst_overloads_probe.out \
  left_shift_inst_2_3 halt_inst_0 \
  "$cake_dir/compiler/backend/stack_removeScript.sml" \
  "$cake_dir/compiler/backend"

# The mlstring carrier probe pins the exact HOL `mlstring = implode string`
# datatype (string = char list, char the 256-element type) needed by the
# stackLang/stack_names program FFI field.
run_probe mlstring_carrier_probeScript.sml mlstring_carrier_probe.out \
  ml_strlen ml_concat_len \
  "$cake_dir/basis/pure/mlstringScript.sml" \
  "$cake_dir/basis/pure"

# The loopSem state-carrier probe pins the exact field shapes of a concrete
# (8,'ffi) loopSem$state: num_map locals/code, total memory, set domain, clock, be.
run_probe loop_sem_state_carrier_probeScript.sml loop_sem_state_carrier_probe.out \
  locals_0 base_self \
  "$cake_dir/pancake/semantics/loopSemScript.sml" \
  "$cake_dir/pancake/semantics"

# The stackLang prog-carrier probe pins the exact `prog` datatype FFI field
# (mlstring) and representative constructor shapes at word type 64.
run_probe stack_lang_prog_carrier_probeScript.sml stack_lang_prog_carrier_probe.out \
  pg_skip pg_ffi_eq \
  "$cake_dir/compiler/backend/stackLangScript.sml" \
  "$cake_dir/compiler/backend"

# The panLang shape probe pins the exact `panLang$shape` name field as
# `mlstring` via `shape_to_str` (Named nm returns nm), plus constructor
# equality and arity.
run_probe pan_lang_shape_probeScript.sml pan_lang_shape_probe.out \
  shp_one_str shp_comb_len \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The loopLang exp/loop_arith probe pins the exact constructor and field shapes
# of the faithful width-indexed carriers HolLoopExp/LoopArith.
run_probe loop_lang_exp_probeScript.sml loop_lang_exp_probe.out \
  exp_const arith_div \
  "$cake_dir/pancake/loopLangScript.sml" \
  "$cake_dir/pancake"

# The loopLang prog probe records HOL constructor outputs for comparison with
# the untagged finite-map approximation (which is not an exact num_set port).
run_probe loop_lang_prog_probeScript.sml loop_lang_prog_probe.out \
  prog_skip prog_ffi \
  "$cake_dir/pancake/loopLangScript.sml" \
  "$cake_dir/pancake"

# The panLang exp probe pins the `exp` word payload (`Const`), its `mlstring`
# identifier fields, and representative constructor arities at word type 64.
run_probe pan_lang_exp_probeScript.sml pan_lang_exp_probe.out \
  ex_const ex_bytesinword \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"
# The num_set/spt probe observes the exact HOL sptree lookup/insert/wf/isEmpty
# behaviour for the unit-spt carrier used as num_set.
run_probe num_set_spt_probeScript.sml num_set_spt_probe.out \
  lookup_ln insert_ovw \
  "$cake_dir/misc/miscScript.sml" \
  "$cake_dir/misc"

# The panLang prog probe pins the `prog` constructor arities, the `mlstring`
# identifier fields, and the word-indexed exp payloads at word type 64.
run_probe pan_lang_prog_probeScript.sml pan_lang_prog_probe.out \
  pg_skip pg_annot_len \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The num_set toAList probe observes the exact HOL sptree enumeration order
# (mixed order, but deterministic).
run_probe num_set_to_alist_probeScript.sml num_set_to_alist_probe.out \
  toalist_ln toalist_four \
  "$cake_dir/misc/miscScript.sml" \
  "$cake_dir/misc"
# The panLang decl probe pins the `fun_decl` / `decl` / `struct_info` field
# shapes (mlstring names, bool flags, param lists, record size) at word type 64.
run_probe pan_lang_decl_probeScript.sml pan_lang_decl_probe.out \
  fd_name_len si_size \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The word_to_stack copy_ret_aux/copy_ret probe pins the return-slot copy
# fragments (list_Seq of StackLoad/StackStore, SeqStackFree) at word type 64.
run_probe word_to_stack_copy_ret_probeScript.sml word_to_stack_copy_ret_probe.out \
  cra_zero cr_handle \
  "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"

# The panLexer byte probe observes the original lexer's ASCII-only identifier
# predicates (HOL char is 8-bit; bytes >= 128 are not alpha/digit).
run_probe pan_lexer_bytes_probeScript.sml pan_lexer_bytes_probe.out \
  plx_alpha_206 plx_ascii_then_high \
  "$cake_dir/pancake/parser/panLexerScript.sml" \
  "$cake_dir/pancake/parser"
# The get_keyword probe pins the original keyword table for every entry plus
# the empty / foreign / plain-identifier fallbacks.
run_probe pan_lexer_get_keyword_probeScript.sml pan_lexer_get_keyword_probe.out \
  gk_skip gk_done \
  "$cake_dir/pancake/parser/panLexerScript.sml" \
  "$cake_dir/pancake/parser"
# The ffi_state carrier probe observes the exact HOL ffi datatype shapes,
# initial_ffi_state and the call_FFI cases (identity, success, length
# failure, oracle final).
run_probe ffi_state_carrier_probeScript.sml ffi_state_carrier_probe.out \
  ffi_outcome_failed call_shmem_final_event \
  "$cake_dir/semantics/ffi/ffiScript.sml" \
  "$cake_dir/semantics/ffi"

# The crepLang exp probe observes the exact width-indexed Crepe expression
# carrier (word payloads and fixed 5-word LoadGlob width).
run_probe crep_lang_exp_probeScript.sml crep_lang_exp_probe.out \
  cexp_const cexp_topaddr \
  "$cake_dir/pancake/crepLangScript.sml" \
  "$cake_dir/pancake"

# The crepLang prog probe observes the exact width-indexed Crepe program
# carrier (MlString Call/ExtCall names, word payloads, fixed 5-word StoreGlob).
run_probe crep_lang_prog_probeScript.sml crep_lang_prog_probe.out \
  prg_skip prg_tick \
  "$cake_dir/pancake/crepLangScript.sml" \
  "$cake_dir/pancake"

run_probe pan_lang_size_of_sh_with_ctxt_probeScript.sml pan_lang_size_of_sh_with_ctxt_probe.out \
  sswc_one sswc_comb_miss \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The mem_load probe observes the exact HOL mem_load over the faithful carriers.
run_probe pan_sem_mem_load_exact_probeScript.sml pan_sem_mem_load_exact_probe.out \
  ml_one_hit ml_comb_offset \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The size_of_shape probe observes the exact context-free HOL size_of_shape.
run_probe pan_lang_size_of_shape_probeScript.sml pan_lang_size_of_shape_probe.out \
  ss_one ss_eq \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The is_wf_shape probe observes is_wf_shape/is_wf_flds/is_wf_ctxt over the
# exact MlString-keyed context, including the duplicate-name and missing-field
# rejections.
run_probe pan_lang_is_wf_shape_probeScript.sml pan_lang_is_wf_shape_probe.out \
  iwf_one iwf_ctxt_field_miss \
  "$cake_dir/pancake/panLangScript.sml" \
  "$cake_dir/pancake"

# The shape_of probe observes the total HOL shape_of over panSem$v.
run_probe pan_sem_shape_of_probeScript.sml pan_sem_shape_of_probe.out \
  so_valword so_wordlab \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The isValWord probe observes the exact boolean `panSem$isValWord` on
# Val/RStruct/NStruct and on the raw Word payload.
run_probe pan_sem_is_val_word_probeScript.sml pan_sem_is_val_word_probe.out \
  is_valword_val is_valword_wordlab \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The empty_locals probe observes the exact `panSem$empty_locals` state update:
# the locals map is cleared while other fields are preserved.
run_probe pan_sem_empty_locals_probeScript.sml pan_sem_empty_locals_probe.out \
  el_lookup el_globals \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The mem_store_32 probe observes the exact four-byte replacement (little and
# big endian), plus the unaligned and out-of-domain NONE cases.
run_probe pan_sem_mem_store_32_probeScript.sml pan_sem_mem_store_32_probe.out \
  ms32_aligned ms32_other_cell \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The result probe observes the exact panSem result constructor shapes.
run_probe pan_sem_result_probeScript.sml pan_sem_result_probe.out \
  res_error res_distinct \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The panSem mem_store/mem_stores probe observes in-domain replacement, pointwise
# preservation of other cells, out-of-domain failure, the bytes_in_word stride (8w
# for 64-bit words), the empty list, and a later-list store failure.
run_probe pan_sem_mem_store_probeScript.sml pan_sem_mem_store_probe.out \
  ms_hit_lookup mss_second_miss \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The shared-memory probe observes panSem `sh_mem_load`/`sh_mem_store`:
# nb = 0 in/out of `sh_memaddrs`, byte-aligned nb = 1, an FFI_final outcome
# clearing locals, and the FFI_return event/state update for both primitives.
run_probe pan_sem_sh_mem_probeScript.sml pan_sem_sh_mem_probe.out \
  l_load_hit_local l_store_final_unchanged \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The declaration-context probe observes panSem `decs_stcnames`: the empty
# context, a well-formed structure, its computed size, duplicate names,
# duplicate field names, an unknown `Named` shape, and skipped decl forms.
run_probe pan_sem_decs_stcnames_probeScript.sml pan_sem_decs_stcnames_probe.out \
  dsc_empty dsc_skip_len \
  "$cake_dir/pancake/semantics/panSemScript.sml"

# The panProps shape_of_val / res_var FLOOKUP probe observes the exact HOL
# shape_of on the Val (word_lab) constructor and the res_var finite-map
# update/delete semantics (panPropsScript.sml:14, :220, :228, :236).
run_probe pan_props_shape_res_var_probeScript.sml pan_props_shape_res_var_probe.out \
  spv_one rv_some \
  "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The pan_commonProps zip/fupdate and disjoint take/drop probe observes the
# finite-map update-not-mem and list-disjointness lemmas
# (pan_commonPropsScript.sml:289, :399, :413).
run_probe pan_common_props_zip_disjoint_probeScript.sml pan_common_props_zip_disjoint_probe.out \
  fzn_notmem ddt_disjoint \
  "$cake_dir/pancake/semantics/pan_commonPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The crepProps assigned_vars / var_cexp probe observes the nested_decs append,
# stores emptiness, and load_shape EXACT lemmas
# (crepPropsScript.sml:390, :400, :429, :439, :215).
run_probe crep_props_assigned_vars_probeScript.sml crep_props_assigned_vars_probe.out \
  avnda vels \
  "$cake_dir/pancake/semantics/crepPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The pan_commonProps fm_update_diff_vars probe observes that updating a finite
# map at `a`, then a distinct `b`, then `a`, then `b` collapses to one update
# at each key (pan_commonPropsScript.sml:780).
run_probe pan_common_props_fm_update_diff_vars_probeScript.sml pan_common_props_fm_update_diff_vars_probe.out \
  fmdv_eq_1 fmdv_lhs_absent \
  "$cake_dir/pancake/semantics/pan_commonPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The panProps size_of_sh_with_ctxt_eq probe observes that a context-free
# well-formed shape has the same with-context size as its plain size_of_shape
# size (panPropsScript.sml:184, using panLang size_of_sh_with_ctxt/size_of_shape).
run_probe pan_props_size_with_ctxt_probeScript.sml pan_props_size_with_ctxt_probe.out \
  ssc_one ssc_eq_nested \
  "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The panSem vshapes_args_rel_imp_eq_len_MAP probe observes the exact
# LIST_REL (λvshape arg. SND vshape = shape_of arg) vshapes args relation and
# its LENGTH / MAP SND / MAP shape_of consequences (panSemScript.sml:740).
run_probe pan_sem_vshapes_args_rel_probeScript.sml pan_sem_vshapes_args_rel_probe.out \
  vra_one vra_map_two \
  "$cake_dir/pancake/semantics/panSemScript.sml" \
  "$cake_dir/pancake/semantics"

# The pan_commonProps take/drop disjoint, EL disjoint, and empty zip lookup
# probe observes pan_commonPropsScript.sml:534, :606, and :575.
run_probe pan_common_props_take_drop_el_zip_probeScript.sml pan_common_props_take_drop_el_zip_probe.out \
  atdd_disjoint nmfz_hit \
  "$cake_dir/pancake/semantics/pan_commonPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The panProps length_flatten_eq_size_of_shape probe observes that under the
# empty-constructor context the flattened length of a well-formed value equals
# its shape size (panPropsScript.sml:171).
run_probe pan_props_length_flatten_probeScript.sml pan_props_length_flatten_probe.out \
  lfs_val lfs_wf_nested \
  "$cake_dir/pancake/semantics/panPropsScript.sml" \
  "$cake_dir/pancake/semantics"

# The pan_to_crep is_wf_shape_nil_length_flatten probe observes the exact
# flatten/size_of_shape relationship under the empty constructor context
# (pan_to_crepProofScript.sml:2469).
run_probe pan_to_crep_is_wf_shape_nil_probeScript.sml pan_to_crep_is_wf_shape_nil_probe.out \
  iwf_val iwf_wf_struct \
  "$cake_dir/pancake/proofs/pan_to_crepProofScript.sml" \
  "$cake_dir/pancake/proofs"

# The pan_globals fresh_name probe observes that the source-shaped fresh-name
# search only ever appends apostrophes (pan_globalsScript.sml:55).
run_probe pan_globals_fresh_name_probeScript.sml pan_globals_fresh_name_probe.out \
  empty absent \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals new_main_name probe observes the synthesized entry-point name
# for representative declaration lists (pan_globalsScript.sml:224).
run_probe pan_globals_new_main_name_probeScript.sml pan_globals_new_main_name_probe.out \
  empty absent \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals fperm_name probe observes the source-shape name permutation
# `fperm_name f g h` (pan_globalsScript.sml:185-188) for unchanged and
# colliding keys, including names that already carry apostrophes.
run_probe pan_globals_fperm_name_probeScript.sml pan_globals_fperm_name_probe.out \
  source_collision fperm_name_done \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

run_probe word_to_stack_handler_probeScript.sml word_to_stack_handler_probe.out \
  shaF pop_eq "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"

run_probe word_to_stack_call_dest_probeScript.sml word_to_stack_call_dest_probe.out \
  cd_some wl_store "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
# The pan_globals fperm probe observes the source-shape program permutation
# `fperm f g p` (pan_globalsScript.sml:191-214) for the recursive control
# constructs, the Call handler case, the DecCall case and the catch-all.
run_probe pan_globals_fperm_probeScript.sml pan_globals_fperm_probe.out \
  recursive_control fperm_done \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals fperm_decs probe observes the source-shape declaration-list
# permutation `fperm_decs f g ds` (pan_globalsScript.sml:216-221) for a mixed
# declaration list and the empty list.
run_probe pan_globals_fperm_decs_probeScript.sml pan_globals_fperm_decs_probe.out \
  mixed singleton_nonfunction \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals resort_decls probe observes the declaration regrouping
# `resort_decls ds` (pan_globalsScript.sml:179-182) for a mixed list, an
# already-grouped list, and the empty list.
run_probe pan_globals_resort_decls_probeScript.sml pan_globals_resort_decls_probe.out \
  mixed empty \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals dec_shapes probe observes the shape projection
# `dec_shapes ds` (pan_globalsScript.sml:228-233) for the empty list, a mixed
# list, and a function-only list.
run_probe pan_globals_dec_shapes_probeScript.sml pan_globals_dec_shapes_probe.out \
  empty functions_only \
  "$cake_dir/pancake/pan_globalsScript.sml" \
  "$cake_dir/pancake"

# The pan_globals MEM_functions probe observes the source-shape membership
# projection described by the local theorem MEM_functions
# (pan_globalsProofScript.sml:2380-2387).  Since `[local]` theorems are not
# exported to the theory database, the probe records the direct EVAL rows for
# `functions` and the membership instance the theorem characterizes.
run_probe pan_globals_mem_functions_probeScript.sml pan_globals_mem_functions_probe.out \
  functions_empty mem_function_entry \
  "$cake_dir/pancake/proofs/pan_globalsProofScript.sml" \
  "$cake_dir/pancake/proofs"

run_probe word_to_stack_stub_probeScript.sml word_to_stack_stub_probe.out \
  pcp_eq pcp_top "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"

# The word_to_stack wShareInst probe observes the shared-memory instruction
# helper `wShareInst` (word_to_stackScript.sml:186-224) for all eight memop
# forms at word type 64.
run_probe word_to_stack_wshareinst_probeScript.sml word_to_stack_wshareinst_probe.out \
  ws_load ws_store32 "$cake_dir/compiler/backend/word_to_stackScript.sml" \
  "$cake_dir/compiler/backend"
