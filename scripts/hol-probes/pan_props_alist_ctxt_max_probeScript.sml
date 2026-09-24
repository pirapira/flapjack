load "bossLib";
load "preamble";
load "panPropsTheory";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open alistTheory;
open finite_mapTheory;
open panPropsTheory panLangTheory;

fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

val sh = ``[panLang$One; panLang$One] : panLang$shape list``;
val ns = ``[0;1] : num list``;
val vs = ``[«a»; «b»] : mlstring list``;
val fm = ``((FEMPTY |++ ZIP (^vs, ZIP (^sh, with_shape ^sh ^ns)))
            : (mlstring, panLang$shape # num list) fmap)``;
val maxns = ``MAX_LIST ^ns``;

val _ = print_eval "ctxt_a_bound"
  (``case FLOOKUP ^fm «a» of
      SOME (s,xs) => EVERY (\(x:num). x <= ^maxns) xs
    | NONE => F``);

val _ = print_eval "ctxt_b_bound"
  (``case FLOOKUP ^fm «b» of
      SOME (s,xs) => EVERY (\(x:num). x <= ^maxns) xs
    | NONE => F``);

val _ = print_eval "ctxt_max_value" (``^maxns = 1``);
