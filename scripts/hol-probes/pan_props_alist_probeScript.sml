(* Direct HOL-EVAL observations for Cake's `all_distinct_alist_no_overlap`
   (`cakeml/pancake/semantics/panPropsScript.sml:476`).

   `no_overlap` is a property, so the rows expose its components as boolean
   projections on the concrete context `sh = [One;One]`, `ns = [0;1]`,
   `vs = ["a";"b"]`. *)
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
val fm = ``((FEMPTY |++ ZIP (^vs, ZIP (^sh, with_shape ^sh ^ns))) :
             (mlstring, panLang$shape # num list) fmap)``;

val _ = print_eval "alist_a_nodup"
  (``case FLOOKUP ^fm «a» of SOME (s, xs) => ALL_DISTINCT xs | NONE => F``);
val _ = print_eval "alist_b_nodup"
  (``case FLOOKUP ^fm «b» of SOME (s, xs) => ALL_DISTINCT xs | NONE => F``);
val _ = print_eval "alist_a_slots"
  (``case FLOOKUP ^fm «a» of SOME (s, xs) => (xs = [0]) | NONE => F``);
val _ = print_eval "alist_b_slots"
  (``case FLOOKUP ^fm «b» of SOME (s, xs) => (xs = [1]) | NONE => F``);
val _ = print_eval "alist_disjoint"
  (``~(MEM (0:num) [1]) /\ ALL_DISTINCT ([0;1] : num list)``);
