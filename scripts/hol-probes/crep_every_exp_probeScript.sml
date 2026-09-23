(* Direct HOL-EVAL observations for the Crepe expression predicate that the
   Lean `crepEveryExp` port must match.

   Reference:
     cakeml/pancake/semantics/crepPropsScript.sml: every_exp_def

   `every_exp P e` holds when `P` holds of `e` and of every subexpression of
   `e`.  The rows below pin the traversal on a concrete satisfying predicate
   (`is_load`) and a concrete unsatisfying one (`is_const`), including a
   nested `Op` argument list.
*)
load "bossLib";
load "preamble";
load "crepPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepPropsTheory;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val is_const =
  ``(λ (e : 8 crepLang$exp). case e of crepLang$Const _ => T | _ => F)``;
val not_op =
  ``(λ (e : 8 crepLang$exp). case e of crepLang$Op _ _ => F | _ => T)``;

val _ = print_eval "const_hit"
  ``every_exp ^is_const (crepLang$Const (1w : 8 word))``;
val _ = print_eval "op_not_const"
  ``every_exp ^is_const
      (crepLang$Op Add [crepLang$Const (1w : 8 word);
                        crepLang$Const (2w : 8 word)])``;
val _ = print_eval "op_argument_not_const"
  ``every_exp ^is_const
      (crepLang$Op Add [crepLang$Const (1w : 8 word);
                        crepLang$Load (crepLang$Const (3w : 8 word))])``;
val _ = print_eval "load_hit"
  ``every_exp ^not_op
      (crepLang$Load (crepLang$Load (crepLang$Const (1w : 8 word))))``;
val _ = print_eval "load_of_op_miss"
  ``every_exp ^not_op
      (crepLang$Load
         (crepLang$Op Add [crepLang$Const (1w : 8 word)]))``;
val _ = print_eval "always_op_nested"
  ``every_exp (λ (e : 8 crepLang$exp). T)
      (crepLang$Op Add [crepLang$Load (crepLang$Const (1w : 8 word));
                        crepLang$Const (2w : 8 word)])``;
