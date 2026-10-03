load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble;
val _ = Globals.linewidth := 1000000;
(* Full original inferred carriers remain visible in every captured statement. *)
val _ = show_types := true;
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");

(* Exported originals of stack_rawcallProofScript.sml:872-941. *)
val _ = checked "reg_bound_comp_statement" stack_rawcallProofTheory.reg_bound_comp;
val _ = checked "stack_rawcall_reg_bound_statement" stack_rawcallProofTheory.stack_rawcall_reg_bound;
val _ = checked "call_args_comp_statement" stack_rawcallProofTheory.call_args_comp;
val _ = checked "stack_alloc_call_args_statement" stack_rawcallProofTheory.stack_alloc_call_args;
val _ = checked "MAP_FST_compile_statement" stack_rawcallProofTheory.MAP_FST_compile;
val _ = checked "call_arg_comp_statement" stack_rawcallProofTheory.call_arg_comp;
