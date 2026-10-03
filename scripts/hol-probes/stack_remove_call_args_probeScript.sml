load "preamble"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble;
val _ = Globals.linewidth := 1000000;
(* Full original inferred carriers remain visible in every captured statement. *)
val _ = show_types := true;
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");

(* Exported original of stack_removeProofScript.sml stack_remove_call_args. *)
val _ = checked "stack_remove_call_args_statement" stack_removeProofTheory.stack_remove_call_args;
