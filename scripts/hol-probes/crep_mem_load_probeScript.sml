(*
  Direct HOL-EVAL probes for Pancake crepSem mem_load.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:48-52.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "mem_load_hit"
  ``crepSem$mem_load (3w : 8 word)
      (^s with <| memaddrs := {3w};
                  memory := (3w =+ Word (7w : 8 word)) (^s).memory |>)``;
val _ = print_eval "mem_load_miss"
  ``crepSem$mem_load (4w : 8 word)
      (^s with <| memaddrs := {3w};
                  memory := (3w =+ Word (7w : 8 word)) (^s).memory |>)``;
