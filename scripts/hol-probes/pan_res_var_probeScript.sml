(* Direct HOL-EVAL probes for CakeML Pancake res_var. *)
load "bossLib";
load "preamble";
load "panSemTheory";
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

val locals = ``(FEMPTY |+ ("x", ValWord (3w : 64 word)))``

val _ = print_eval "delete_hit"
  ``FLOOKUP (res_var ^locals ("x", NONE)) "x"``
val _ = print_eval "delete_other"
  ``FLOOKUP (res_var ^locals ("y", NONE)) "x"``
val _ = print_eval "update_hit"
  ``FLOOKUP (res_var ^locals ("x", SOME (ValWord (7w : 64 word)))) "x"``
