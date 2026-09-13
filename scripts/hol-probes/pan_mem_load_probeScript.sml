(*
  Direct HOL-EVAL probes for CakeML Pancake panSem$mem_load.
  The output is checked into pan_mem_load_probe.out and is consumed by Lean
  parity tests; this script is not a second implementation.
*)
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

val _ = print_eval "one_hit"
  ``mem_load One (10w : 64 word) {10w}
      (\a : 64 word. Word 3w) []``
val _ = print_eval "one_miss"
  ``mem_load One (11w : 64 word) {10w}
      (\a : 64 word. Word 3w) []``
val _ = print_eval "comb_hit"
  ``mem_load (Comb [One; One]) (10w : 64 word) {10w;18w}
      (\a : 64 word. if a = 10w then Word 3w else Word 5w) []``
val _ = print_eval "named_hit"
  ``mem_load (Named (strlit "Pair")) (10w : 64 word) {10w;18w}
      (\a : 64 word. if a = 10w then Word 3w else Word 5w)
      [(strlit "Pair", <| fields := [(strlit "left", One);
                                      (strlit "right", One)]; size := 2 |>)]``
val _ = print_eval "named_suffix_blocked"
  ``mem_load (Named (strlit "Outer")) (10w : 64 word) {10w}
      (\a : 64 word. Word 3w)
      [(strlit "Later", <| fields := []; size := 1 |>);
       (strlit "Outer", <| fields := [(strlit "later", Named (strlit "Later"))];
                             size := 1 |>)]``
