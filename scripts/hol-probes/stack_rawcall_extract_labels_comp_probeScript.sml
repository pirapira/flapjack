load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
(* Full original inferred carriers remain visible in every captured statement. *)
val _ = show_types := true;
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");

(* Exported original of stack_rawcallProofScript.sml:818-832. *)
val _ = checked "extract_labels_comp_statement" extract_labels_comp;
