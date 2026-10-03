load "preamble"; load "stack_namesTheory";
open HolKernel Parse bossLib preamble stack_namesTheory;
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

(* Typed originals of stack_namesScript.sml prog_comp_def and compile_def: the section name is a type variable. *)
val _ = checked "prog_comp_def_statement" stack_namesTheory.prog_comp_def;
val _ = typed_statement "prog_comp_def_statement_typed" stack_namesTheory.prog_comp_def;
val _ = type_list "prog_comp_def_statement_types" stack_namesTheory.prog_comp_def;
val _ = checked "compile_def_statement" stack_namesTheory.compile_def;
val _ = typed_statement "compile_def_statement_typed" stack_namesTheory.compile_def;
val _ = type_list "compile_def_statement_types" stack_namesTheory.compile_def;
val _ = (print "compile_string_names="; print_term (rconc (EVAL ``compile (sptree$insert 3 7 sptree$LN) [("a",Halt 3);("b",Return 4)] : (string # 8 stackLang$prog) list``)); print "\n");
