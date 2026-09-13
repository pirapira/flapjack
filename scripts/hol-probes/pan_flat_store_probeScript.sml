(* Direct HOL-EVAL probes for CakeML Pancake word stores. *)
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

val _ = print_eval "store_hit"
  ``(case mem_store 10w (Word 3w) {10w}
        (\a : 64 word. Word 0w) of
      | SOME m => SOME (m 10w)
      | NONE => NONE)``
val _ = print_eval "store_miss"
  ``(case mem_store 11w (Word 3w) {10w}
        (\a : 64 word. Word 0w) of
      | SOME m => SOME (m 11w)
      | NONE => NONE)``
val _ = print_eval "stores_hit"
  ``(case mem_stores 10w [Word 3w; Word 5w] {10w;18w}
        (\a : 64 word. Word 0w) of
      | SOME m => SOME (m 10w, m 18w)
      | NONE => NONE)``
val _ = print_eval "stores_blocked"
  ``(case mem_stores 10w [Word 3w; Word 5w] {10w}
        (\a : 64 word. Word 0w) of
      | SOME m => SOME (m 10w, m 18w)
      | NONE => NONE)``
