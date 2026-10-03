load "preamble"; load "stack_namesProofTheory";
open HolKernel Parse bossLib preamble stack_namesProofTheory;
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

(* Typed original of stack_namesProofScript.sml MAP_FST_compile. *)
val _ = checked "MAP_FST_compile_statement" stack_namesProofTheory.MAP_FST_compile;
val _ = typed_statement "MAP_FST_compile_statement_typed" stack_namesProofTheory.MAP_FST_compile;
val _ = type_list "MAP_FST_compile_statement_types" stack_namesProofTheory.MAP_FST_compile;
