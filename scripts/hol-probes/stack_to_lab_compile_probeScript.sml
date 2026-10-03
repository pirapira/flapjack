load "preamble"; load "stack_to_labTheory"; load "bvl_to_bviTheory";
open HolKernel Parse bossLib preamble stack_to_labTheory;
val _ = Globals.linewidth := 1000000;
(* Full original inferred carriers remain visible in every captured statement. *)
val _ = show_types := true;
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");

(* Exported originals of stack_to_labScript.sml:138-167 and their stub-location
   prerequisites (backend_commonScript.sml:132, bvl_to_bviScript.sml:106-114). *)
val _ = checked "is_gen_gc_def_statement" is_gen_gc_def;
val _ = checked "config_accessors_statement" config_accessors;
val _ = checked "compile_def_statement" stack_to_labTheory.compile_def;
val _ = checked "compile_no_stubs_def_statement" compile_no_stubs_def;
val _ = checked "data_num_stubs_def_statement" backend_commonTheory.data_num_stubs_def;
val _ = checked "AllocGlobal_location_def_statement" bvl_to_bviTheory.AllocGlobal_location_def;
val _ = checked "CopyGlobals_location_def_statement" bvl_to_bviTheory.CopyGlobals_location_def;
val _ = checked "InitGlobals_location_def_statement" bvl_to_bviTheory.InitGlobals_location_def;
val _ = print "is_gen_gc_type=";
val _ = print (type_to_string (type_of ``stack_to_lab$is_gen_gc``));
val _ = print "\n";
val _ = print "compile_type=";
val _ = print (type_to_string (type_of ``stack_to_lab$compile``));
val _ = print "\n";
val _ = print "compile_no_stubs_type=";
val _ = print (type_to_string (type_of ``stack_to_lab$compile_no_stubs``));
val _ = print "\n";
