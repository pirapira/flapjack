(* Direct HOL-EVAL probes for crepLang$load_globals.
   Reference: cakeml/pancake/crepLangScript.sml:116-120. *)
load "bossLib";
load "preamble";
load "../crepLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "empty"
  ``crepLang$load_globals (3w : 5 word) 0``;
val _ = print_eval "one"
  ``crepLang$load_globals (3w : 5 word) 1``;
val _ = print_eval "three"
  ``crepLang$load_globals (3w : 5 word) 3``;
