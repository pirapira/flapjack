(*
  Probe outputs for the original CakeML Pancake loop_to_word definitions.
  This is intentionally a HOL script rather than a second implementation.
  The checked-in output is captured from a direct HOL invocation of this file.
*)
load "bossLib";
load "preamble";
load "loop_to_wordTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "find_var_empty" ``find_var LN 0``
val _ = print_eval "find_var_hit" ``find_var (insert 3 7 LN) 3``
val _ = print_eval "find_var_miss" ``find_var (insert 3 7 LN) 4``
val _ = print_eval "find_var_ctxt_10" ``find_var (make_ctxt 2 [10;11;12] LN) 10``
val _ = print_eval "find_var_ctxt_11" ``find_var (make_ctxt 2 [10;11;12] LN) 11``
val _ = print_eval "find_var_ctxt_12" ``find_var (make_ctxt 2 [10;11;12] LN) 12``
val _ = print_eval "find_reg_imm_imm" ``find_reg_imm LN (Imm 5w : 64 reg_imm)``
val _ = print_eval "find_reg_imm_reg" ``find_reg_imm LN (Reg 11 : 64 reg_imm)``
val _ = print_eval "find_reg_imm_ctxt" ``find_reg_imm (make_ctxt 2 [10;11;12] LN) (Reg 11 : 64 reg_imm)``

(* comp_exp_def, loop_to_wordScript.sml:22-35 *)
val _ = print_eval "comp_exp_const"
  ``comp_exp LN (Const (7w : 8 word))``
val _ = print_eval "comp_exp_var"
  ``comp_exp (insert 3 6 LN) (Var 3)``
val _ = print_eval "comp_exp_lookup"
  ``comp_exp (LN : num num_map) (loopLang$Lookup (9w : 5 word))``
val _ = print_eval "comp_exp_base_addr"
  ``comp_exp (LN : num num_map) loopLang$BaseAddr``
val _ = print_eval "comp_exp_top_addr"
  ``comp_exp (LN : num num_map) loopLang$TopAddr``
val _ = print_eval "comp_exp_nested_op"
  ``comp_exp (insert 3 6 (LN : num num_map))
      (loopLang$Op Add [Const (1w : 8 word); Var 3])``

(* toNumSet_def, loop_to_wordScript.sml:42-44 *)
val _ = print_eval "to_num_set_empty"
  ``toAList (toNumSet [])``
val _ = print_eval "to_num_set_ordered"
  ``toAList (toNumSet [1; 2; 3])``
val _ = print_eval "to_num_set_duplicate"
  ``toAList (toNumSet [3; 1; 3; 2])``

(* fromNumSet_def, loop_to_wordScript.sml:47-48 *)
val _ = print_eval "from_num_set_empty"
  ``fromNumSet (toNumSet [])``
val _ = print_eval "from_num_set_ordered"
  ``fromNumSet (toNumSet [1; 2; 3])``
val _ = print_eval "from_num_set_duplicate"
  ``fromNumSet (toNumSet [3; 1; 3; 2])``

(* mk_new_cutset_def, loop_to_wordScript.sml:51-53 *)
val _ = print_eval "mk_new_cutset_empty"
  ``toAList (mk_new_cutset (insert 3 6 LN) (toNumSet []))``
val _ = print_eval "mk_new_cutset_mapped"
  ``toAList (mk_new_cutset (insert 3 6 LN) (toNumSet [1; 2; 3]))``
val _ = print_eval "mk_new_cutset_duplicate"
  ``toAList (mk_new_cutset (insert 3 6 LN) (toNumSet [3; 1; 3; 2]))``

(* comp_def, loop_to_wordScript.sml:56-150 *)
val _ = print_eval "comp_skip"
  ``comp (LN : num num_map) loopLang$Skip (0,0)``
val _ = print_eval "comp_assign_const"
  ``comp (insert 3 6 LN) (loopLang$Assign 3 (Const (7w : 8 word))) (0,0)``
val _ = print_eval "comp_seq_tick"
  ``comp (LN : num num_map) (loopLang$Seq loopLang$Skip loopLang$Tick) (0,0)``
val _ = print_eval "comp_loop"
  ``comp (insert 3 6 LN)
      (loopLang$Loop (toNumSet [3]) loopLang$Skip (toNumSet [])) (0,0)``
val _ = print_eval "comp_break"
  ``comp (LN : num num_map) (loopLang$Break 2) (0,0)``
val _ = print_eval "comp_fail"
  ``comp (LN : num num_map) loopLang$Fail (0,0)``
val _ = print_eval "comp_set_global"
  ``comp (LN : num num_map)
      (loopLang$SetGlobal (9w : 5 word) (Const (7w : 8 word))) (0,0)``
