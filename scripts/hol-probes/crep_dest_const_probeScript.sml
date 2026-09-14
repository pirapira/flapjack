(* Direct HOL-EVAL fixture for crep_arith$dest_const_def. *)
load "bossLib";
load "preamble";
load "crep_arithTheory";
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

val _ = print_eval "const"
  ``crep_arith$dest_const (crepLang$Const 7w)``;
val _ = print_eval "var"
  ``crep_arith$dest_const (crepLang$Var 2)``;
val _ = print_eval "load"
  ``crep_arith$dest_const (crepLang$Load (crepLang$Const 3w))``;
val _ = print_eval "mul"
  ``crep_arith$dest_const
      (crepLang$Crepop crepLang$Mul [crepLang$Const 2w; crepLang$Const 4w])``;
