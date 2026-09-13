(* Direct HOL-EVAL probes for CakeML Pancake value flattening. *)
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

val _ = print_eval "word"
  ``flatten (ValWord (3w : 64 word))``
val _ = print_eval "record"
  ``flatten (RStruct [ValWord (3w : 64 word);
                     RStruct [ValWord (5w : 64 word); ValWord (7w : 64 word)]])``
val _ = print_eval "named"
  ``flatten (NStruct (strlit "Pair")
      [(strlit "left", ValWord (3w : 64 word));
       (strlit "right", RStruct [ValWord (5w : 64 word);
                                  ValWord (7w : 64 word)])])``
