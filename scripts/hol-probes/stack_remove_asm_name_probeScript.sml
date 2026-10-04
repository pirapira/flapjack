load "preamble"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory;
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
(* Exported originals of stack_removeProofScript.sml:4209-4300. *)

val _ = checked "stack_remove_comp_stack_asm_name_statement" stack_remove_comp_stack_asm_name;
val _ = typed_statement "stack_remove_comp_stack_asm_name_statement_typed" stack_remove_comp_stack_asm_name;
val _ = type_list "stack_remove_comp_stack_asm_name_statement_types" stack_remove_comp_stack_asm_name;
val _ = checked "stack_remove_stack_asm_name_statement" stack_remove_stack_asm_name;
val _ = typed_statement "stack_remove_stack_asm_name_statement_typed" stack_remove_stack_asm_name;
val _ = type_list "stack_remove_stack_asm_name_statement_types" stack_remove_stack_asm_name;
