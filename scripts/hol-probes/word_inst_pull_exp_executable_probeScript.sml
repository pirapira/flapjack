load "preamble"; load "word_instTheory";
open HolKernel Parse bossLib preamble wordLangTheory word_instTheory asmTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
fun checked label th =
  (if null (hyp th) then () else raise Fail ("open HOL hypotheses: " ^ label);
   print (label ^ "="); print_term (concl th); print "\n");
val _ = checked "pull_exp_definition" pull_exp_def;
val _ = checked "optimize_consts_definition" optimize_consts_def;
val _ = checked "word_op_definition" word_op_def;
val _ = print "pull_exp_type=";
val _ = print (type_to_string (type_of ``word_inst$pull_exp``));
val _ = print "\n";
val _ = show_types := false;
fun evald name tm = let
  val th = EVAL tm
  val _ = if null (hyp th) then () else raise Fail ("hyp " ^ name)
in rhs (concl th) end;
val _ = (print "add_empty="; print_term (evald "add_empty" ``pull_exp (Op Add [] : 64 wordLang$exp)``); print "\n");
val _ = (print "and_empty="; print_term (evald "and_empty" ``pull_exp (Op And [] : 64 wordLang$exp)``); print "\n");
val _ = (print "or_empty="; print_term (evald "or_empty" ``pull_exp (Op Or [] : 64 wordLang$exp)``); print "\n");
val _ = (print "xor_empty="; print_term (evald "xor_empty" ``pull_exp (Op Xor [] : 64 wordLang$exp)``); print "\n");
val _ = (print "sub_empty="; print_term (evald "sub_empty" ``pull_exp (Op Sub [] : 64 wordLang$exp)``); print "\n");
val _ = (print "sub_single="; print_term (evald "sub_single" ``pull_exp (Op Sub [Const 5w] : 64 wordLang$exp)``); print "\n");
val _ = (print "sub_pair="; print_term (evald "sub_pair" ``pull_exp (Op Sub [Const 9w; Const 4w] : 64 wordLang$exp)``); print "\n");
val _ = (print "sub_var_const="; print_term (evald "sub_var_const" ``pull_exp (Op Sub [Var 1; Const 3w] : 64 wordLang$exp)``); print "\n");
val _ = (print "sub_three="; print_term (evald "sub_three" ``pull_exp (Op Sub [Const 9w; Const 4w; Const 2w] : 64 wordLang$exp)``); print "\n");
val _ = (print "add_constants="; print_term (evald "add_constants" ``pull_exp (Op Add [Const 3w; Const 5w; Const 7w] : 64 wordLang$exp)``); print "\n");
val _ = (print "add_mixed="; print_term (evald "add_mixed" ``pull_exp (Op Add [Var 1; Const 3w; Var 2; Const 5w; Var 3] : 64 wordLang$exp)``); print "\n");
val _ = (print "add_no_constants="; print_term (evald "add_no_constants" ``pull_exp (Op Add [Var 1; Var 2; Var 3] : 64 wordLang$exp)``); print "\n");
val _ = (print "nested_add="; print_term (evald "nested_add" ``pull_exp (Op Add [Var 1; Op Add [Const 3w; Var 2]; Const 5w] : 64 wordLang$exp)``); print "\n");
val _ = (print "xor_cancel="; print_term (evald "xor_cancel" ``pull_exp (Op Xor [Var 1; Const 7w; Const 7w] : 64 wordLang$exp)``); print "\n");
val _ = (print "and_zero="; print_term (evald "and_zero" ``pull_exp (Op And [Var 1; Const 0w] : 64 wordLang$exp)``); print "\n");
val _ = (print "and_all_ones="; print_term (evald "and_all_ones" ``pull_exp (Op And [Var 1; Const 0xFFFFFFFFFFFFFFFFw] : 64 wordLang$exp)``); print "\n");
val _ = (print "or_constants="; print_term (evald "or_constants" ``pull_exp (Op Or [Const 3w; Const 8w] : 64 wordLang$exp)``); print "\n");
val _ = (print "xor_constants="; print_term (evald "xor_constants" ``pull_exp (Op Xor [Const 3w; Const 5w] : 64 wordLang$exp)``); print "\n");
val _ = (print "load_nested="; print_term (evald "load_nested" ``pull_exp (Load (Op Add [Var 1; Const 16w]) : 64 wordLang$exp)``); print "\n");
val _ = (print "shift_nested="; print_term (evald "shift_nested" ``pull_exp (Shift Lsl (Op Xor [Const 3w; Const 5w]) (Const 2w) : 64 wordLang$exp)``); print "\n");
val _ = (print "lookup="; print_term (evald "lookup" ``pull_exp (Lookup CurrHeap : 64 wordLang$exp)``); print "\n");
val _ = (print "width1_wrap="; print_term (evald "width1_wrap" ``pull_exp (Op Add [Const 1w; Const 1w] : 1 wordLang$exp)``); print "\n");
val _ = (print "width32_wrap="; print_term (evald "width32_wrap" ``pull_exp (Op Add [Const 0xFFFFFFFFw; Const 1w] : 32 wordLang$exp)``); print "\n");
val _ = (print "width64_wrap="; print_term (evald "width64_wrap" ``pull_exp (Op Add [Const 0xFFFFFFFFFFFFFFFFw; Const 1w] : 64 wordLang$exp)``); print "\n");
