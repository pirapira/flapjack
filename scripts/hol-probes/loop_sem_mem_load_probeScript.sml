(*
  Direct HOL-EVAL probes for Pancake loopSem mem_load.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:64-69.
  mem_load checks mdomain before reading the original memory function.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(8,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "mem_load_hit"
  ``loopSem$mem_load (3w : 8 word)
      (^s with <| mdomain := {3w};
                  memory := (3w =+ Word (7w : 8 word)) (^s).memory |>)``
val _ = print_eval "mem_load_miss"
  ``loopSem$mem_load (4w : 8 word)
      (^s with <| mdomain := {3w};
                  memory := (3w =+ Word (7w : 8 word)) (^s).memory |>)``
