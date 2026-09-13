(* Direct HOL-EVAL probes for CakeML Pancake panSem$shape_of_def. *)
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

val _ = print_eval "word" ``shape_of (ValWord 3w)``
val _ = print_eval "rstruct" ``shape_of (RStruct [ValWord 3w; ValWord 5w])``
val _ = print_eval "nstruct"
  ``shape_of (NStruct (strlit "Pair")
      [(strlit "left", ValWord 3w); (strlit "right", ValWord 5w)])``
