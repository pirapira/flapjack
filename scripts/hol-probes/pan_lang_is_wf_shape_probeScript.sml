load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val ctxt = ``[(«A», <| fields := [(«f», One)] ; size := 2n |>)] : (stcname # struct_info) list``;
val ctxtOk = ``[(«A», <| fields := [(«f», Named «B»)] ; size := 2n |>) ; («B», <| fields := ([] : (fldname # shape) list) ; size := 1n |>)] : (stcname # struct_info) list``;
val ctxtDup = ``[(«A», <| fields := ([] : (fldname # shape) list) ; size := 1n |>) ; («A», <| fields := ([] : (fldname # shape) list) ; size := 1n |>)] : (stcname # struct_info) list``;
val ctxtFieldMiss = ``[(«A», <| fields := [(«f», Named «B»)] ; size := 2n |>)] : (stcname # struct_info) list``;

val _ = print_eval "iwf_one" ``is_wf_shape ^ctxt One``;
val _ = print_eval "iwf_comb" ``is_wf_shape ^ctxt (Comb [One; Comb [One]])``;
val _ = print_eval "iwf_named_hit" ``is_wf_shape ^ctxt (Named «A»)``;
val _ = print_eval "iwf_named_miss" ``is_wf_shape ^ctxt (Named «Z»)``;
val _ = print_eval "iwf_flds_ok" ``is_wf_flds ^ctxt [(«f», One)]``;
val _ = print_eval "iwf_flds_miss" ``is_wf_flds ^ctxt [(«f», Named «Z»)]``;
val _ = print_eval "iwf_ctxt_ok" ``is_wf_ctxt ^ctxtOk``;
val _ = print_eval "iwf_ctxt_dup" ``is_wf_ctxt ^ctxtDup``;
val _ = print_eval "iwf_ctxt_field_miss" ``is_wf_ctxt ^ctxtFieldMiss``;
