(* Direct HOL-EVAL probes for CakeML Pancake crepSem res_var_def. *)
(* Reference: cakeml/pancake/semantics/crepSemScript.sml:163-166. *)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL (rconc (QCONV (SIMP_CONV (srw_ss()) []) q))
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val locals = ``(FEMPTY |+ (1, Word (3w : 64 word)))``;

val _ = print_eval "res_var_delete_hit"
  ``FLOOKUP (crepSem$res_var ^locals (1, NONE)) 1``;
val _ = print_eval "res_var_update_hit"
  ``FLOOKUP (crepSem$res_var ^locals (1, SOME (Word (7w : 64 word)))) 1``;
