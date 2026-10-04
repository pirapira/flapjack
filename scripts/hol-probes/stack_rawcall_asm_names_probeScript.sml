load "preamble"; load "stack_rawcallProofTheory";
open HolKernel Parse bossLib preamble stack_rawcallProofTheory;
val _ = Globals.linewidth := 1000000;
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");
fun typed_statement label th =
  (show_types := true;
   print (label ^ "="); print_term (concl th); print "\n";
   show_types := false);
fun type_list label th =
  (show_types := true;
   print (label ^ "=");
   app (fn v => print (term_to_string v ^ ":" ^ type_to_string (type_of v) ^ ";"))
     (fst (strip_forall (concl th)) @ free_vars (concl th));
   print "\n";
   show_types := false);
(* Exported originals of stack_rawcallProofScript.sml:838-869. *)

val _ = checked "stack_asm_name_comp_statement" stack_rawcallProofTheory.stack_asm_name_comp;
val _ = typed_statement "stack_asm_name_comp_statement_typed" stack_rawcallProofTheory.stack_asm_name_comp;
val _ = type_list "stack_asm_name_comp_statement_types" stack_rawcallProofTheory.stack_asm_name_comp;
val _ = checked "stack_alloc_stack_asm_convs_statement" stack_rawcallProofTheory.stack_alloc_stack_asm_convs;
val _ = typed_statement "stack_alloc_stack_asm_convs_statement_typed" stack_rawcallProofTheory.stack_alloc_stack_asm_convs;
val _ = type_list "stack_alloc_stack_asm_convs_statement_types" stack_rawcallProofTheory.stack_alloc_stack_asm_convs;
