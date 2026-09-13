(*
  Direct HOL-EVAL probes for Pancake loopSem mem_store.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:57-62.
  mem_store succeeds only on the machine-memory domain and updates the
  original memory map at the requested address.
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

val _ = print_eval "mem_store_hit"
  ``case loopSem$mem_store (3w : 8 word) (Word (7w : 8 word))
      (^s with <| mdomain := {3w};
                  memory := (3w =+ Word (1w : 8 word)) (^s).memory |>) of
       NONE => NONE | SOME s' => loopSem$mem_load (3w : 8 word) s'``
val _ = print_eval "mem_store_miss"
  ``loopSem$mem_store (4w : 8 word) (Word (7w : 8 word))
      (^s with <| mdomain := {3w};
                  memory := (3w =+ Word (1w : 8 word)) (^s).memory |>)``
val _ = print_eval "mem_store_other"
  ``case loopSem$mem_store (3w : 8 word) (Word (7w : 8 word))
      (^s with <| mdomain := {3w; 4w};
                  memory := (4w =+ Word (1w : 8 word)) (^s).memory |>) of
       NONE => NONE | SOME s' => loopSem$mem_load (4w : 8 word) s'``
