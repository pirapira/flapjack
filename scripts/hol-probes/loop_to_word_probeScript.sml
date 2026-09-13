(*
  Probe outputs for the original CakeML Pancake loop_to_word definitions.
  This is intentionally a HOL script rather than a second implementation.
  The checked-in output is regenerated with scripts/hol-probes/regenerate.sh.
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
