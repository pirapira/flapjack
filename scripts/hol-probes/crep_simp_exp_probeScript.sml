(* Direct HOL-EVAL fixture for crep_arith$simp_exp_def plus a successful
   crepSem$eval observation before and after a representative simplification.
   References: cakeml/pancake/crep_arithScript.sml:50-64 and
   cakeml/pancake/semantics/crepSemScript.sml:90-137. *)
load "bossLib";
load "preamble";
load "crepSemTheory";
load "crep_arithTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

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

(* HOL eval sees a local value 5 and multiplication by 8. simp_exp rewrites
   this to a left shift by 3; both original eval results are Word 40. *)
val s64 = ``(s:(64,unit) crepSem$state)``;
val eval_state =
  ``^s64 with <| locals := FEMPTY |+ (2, Word (5w:64 word)) |>``;
val eval_mul =
  ``crepLang$Crepop crepLang$Mul
      [crepLang$Var 2; crepLang$Const (8w:64 word)]``;
val _ = print_eval "mul_eight_shape"
  ``crep_arith$simp_exp ^eval_mul``;
val _ = print_eval "eval_simp_before"
  ``crepSem$eval ^eval_state ^eval_mul``;
val _ = print_eval "eval_simp_after"
  ``crepSem$eval ^eval_state (crep_arith$simp_exp ^eval_mul)``;
