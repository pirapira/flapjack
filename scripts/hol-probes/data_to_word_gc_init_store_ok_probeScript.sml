load "preamble"; load "data_to_word_gcProofTheory";
open HolKernel Parse bossLib preamble data_to_word_gcProofTheory;
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
(* Exported original of data_to_word_gcProofScript.sml:4569-4599. *)
val _ = checked "init_store_ok_def_statement" init_store_ok_def;
val _ = typed_statement "init_store_ok_def_statement_typed" init_store_ok_def;
val _ = type_list "init_store_ok_def_statement_types" init_store_ok_def;
val _ = checked "gc_fun_ok_word_gc_fun_statement" gc_fun_ok_word_gc_fun;
val _ = typed_statement "gc_fun_ok_word_gc_fun_statement_typed" gc_fun_ok_word_gc_fun;
val _ = type_list "gc_fun_ok_word_gc_fun_statement_types" gc_fun_ok_word_gc_fun;
