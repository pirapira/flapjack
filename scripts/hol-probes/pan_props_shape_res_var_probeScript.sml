(* Direct HOL-EVAL probes for CakeML Pancake panProps shape_of_val and
   res_var FLOOKUP lemmas (panPropsScript.sml:14, :220, :228, :236). *)
load "bossLib";
load "preamble";
load "panSemTheory";
load "panPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val locals = ``(FEMPTY |+ ("x", ValWord (3w : 64 word)))``

val _ = print_eval "spv_one"
  ``shape_of (ValWord (5w : 64 word))``
val _ = print_eval "rv_hit"
  ``FLOOKUP (res_var ^locals ("x", SOME (ValWord (7w : 64 word)))) "x"``
val _ = print_eval "rv_miss"
  ``FLOOKUP (res_var ^locals ("y", SOME (ValWord (7w : 64 word)))) "x"``
val _ = print_eval "rv_diff"
  ``(FLOOKUP (res_var ^locals ("y", NONE)) "x" = FLOOKUP ^locals "x")``
val _ = print_eval "rv_some"
  ``(FLOOKUP (res_var ^locals ("x", FLOOKUP ^locals "x")) "x" =
     FLOOKUP ^locals "x")``
