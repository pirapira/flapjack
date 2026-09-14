(* Direct HOL-EVAL fixture for crep_arith$simp_exp_def. *)
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

val _ = print_eval "const_mul"
  ``crep_arith$simp_exp
      (Crepop Mul [Const (2w : 8 word); Const (3w : 8 word)])``;
val _ = print_eval "left_const"
  ``crep_arith$simp_exp
      (Crepop Mul [Const (2w : 8 word); Var 2])``;
val _ = print_eval "right_const"
  ``crep_arith$simp_exp
      (Crepop Mul [Var 2; Const (2w : 8 word)])``;
val _ = print_eval "odd_const"
  ``crep_arith$simp_exp
      (Crepop Mul [Var 2; Const (3w : 8 word)])``;
val _ = print_eval "nested_const"
  ``crep_arith$simp_exp
      (Crepop Mul [Crepop Mul [Const (2w : 8 word); Const (3w : 8 word)];
                   Const (4w : 8 word)])``;
val _ = print_eval "load_child"
  ``crep_arith$simp_exp
      (Load (Crepop Mul [Var 2; Const (2w : 8 word)]))``;
val _ = print_eval "op_child"
  ``crep_arith$simp_exp
      (Op Add [Crepop Mul [Var 2; Const (2w : 8 word)]])``;
val _ = print_eval "mul_vars"
  ``crep_arith$simp_exp (Crepop Mul [Var 2; Var 3])``;
val _ = print_eval "fallback_var"
  ``crep_arith$simp_exp (Var 7)``;
