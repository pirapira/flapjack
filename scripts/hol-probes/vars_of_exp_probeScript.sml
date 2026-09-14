(* Direct HOL-EVAL fixture for loop_live$vars_of_exp_def. *)
load "bossLib";
load "preamble";
load "loop_liveTheory";
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

val _ = print_eval "var"
  ``loop_live$vars_of_exp (Var 3 : 8 word loopLang$exp) LN``
val _ = print_eval "const_existing"
  ``loop_live$vars_of_exp (Const (7w : 8 word)) (insert 9 () LN)``
val _ = print_eval "load_var"
  ``loop_live$vars_of_exp
      (Load (Var 4 : 8 word loopLang$exp)) (insert 9 () LN)``
val _ = print_eval "op_add_vars"
  ``loop_live$vars_of_exp
      (Op Add [Var 3; Const (1w : 8 word); Var 2]) LN``
val _ = print_eval "shift_nested"
  ``loop_live$vars_of_exp
      (Shift Lsl (Var 6) (Load (Var 1 : 8 word loopLang$exp)))
      (insert 8 () LN)``
