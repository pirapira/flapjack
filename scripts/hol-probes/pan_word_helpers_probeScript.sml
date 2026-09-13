(* Direct HOL-EVAL probes for CakeML Pancake panSem word/value helpers. *)
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

val _ = print_eval "is_word" ``isWord (Word 3w)``
val _ = print_eval "the_word" ``theWord (Word 3w)``
val _ = print_eval "is_val_word" ``isValWord (ValWord 3w)``
val _ = print_eval "is_val_struct"
  ``isValWord (RStruct [ValWord 3w])``
val _ = print_eval "the_val_word" ``theValWord (ValWord 3w)``
