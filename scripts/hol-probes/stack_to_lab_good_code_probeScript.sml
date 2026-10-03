load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble stack_to_labProofTheory;
val _ = Globals.linewidth := 1000000;
(* Full original inferred carriers remain visible in every captured statement. *)
val _ = show_types := true;
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");

(* Exported originals of stack_to_labProofScript.sml:3349-3363. *)
val _ = checked "good_code_def_statement" good_code_def;
val _ = checked "contain_def_statement" contain_def;
val _ = print "good_code_type=";
val _ = print (type_to_string (type_of ``stack_to_labProof$good_code``));
val _ = print "\n";
val _ = print "contain_type=";
val _ = print (type_to_string (type_of ``stack_to_labProof$contain``));
val _ = print "\n";
