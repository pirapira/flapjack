(* Direct HOL-EVAL probes for CakeML Pancake Loop dec_clock_def. *)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:('a,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "dec_clock_five"
  ``(dec_clock (^s with clock := 5)).clock``
val _ = print_eval "dec_clock_zero"
  ``(dec_clock (^s with clock := 0)).clock``
val _ = print_eval "dec_clock_local"
  ``get_vars [1] (dec_clock (^s with locals := insert 1 (Word 7w) LN))``
