(* Direct HOL-EVAL probes for pan_to_crep$cexp_heads.
   Reference: cakeml/pancake/pan_to_crepScript.sml:19-26. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "empty"
  ``pan_to_crep$cexp_heads
      ([] : (8 word crepLang$exp) list list)``;
val _ = print_eval "heads"
  ``pan_to_crep$cexp_heads
      [[Const (1w : 8 word); Const 2w]; [Var 3; Var 4]]``;
val _ = print_eval "empty_head"
  ``pan_to_crep$cexp_heads
      [[]; [Const (5w : 8 word)]]``;
val _ = print_eval "empty_tail"
  ``pan_to_crep$cexp_heads
      [[Const (6w : 8 word)]; []]``;
