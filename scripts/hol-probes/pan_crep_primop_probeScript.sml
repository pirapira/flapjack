(* Direct HOL-EVAL oracle for panSem$pan_primop, crepSem$crep_primop,
   and word-labeled flattening across the AddCarry bridge. *)
load "bossLib";
load "preamble";
load "../semantics/panSemTheory";
load "../semantics/crepSemTheory";
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
  end;

val _ = print_eval "pan_valid"
  ``OPTION_MAP (MAP (w2n o panSem$theWord) o panSem$flatten)
      (panSem$pan_primop AddCarry
        [ValWord (3w : 8 word); ValWord 4w;
         ValWord 2w])``;
val _ = print_eval "pan_overflow"
  ``OPTION_MAP (MAP (w2n o panSem$theWord) o panSem$flatten)
      (panSem$pan_primop AddCarry
        [ValWord (255w : 8 word); ValWord 0w;
         ValWord 1w])``;
val _ = print_eval "pan_invalid"
  ``panSem$pan_primop AddCarry
      [ValWord (3w : 8 word); RStruct [];
       ValWord 0w]``;
val _ = print_eval "crep_valid"
  ``OPTION_MAP (MAP (w2n o panSem$theWord))
      (crepSem$crep_primop AddCarry
        [Word (3w : 8 word); Word 4w;
         Word 2w])``;
val _ = print_eval "crep_overflow"
  ``OPTION_MAP (MAP (w2n o panSem$theWord))
      (crepSem$crep_primop AddCarry
        [Word (255w : 8 word); Word 0w;
         Word 1w])``;
val _ = print_eval "crep_invalid"
  ``crepSem$crep_primop AddCarry
      [Word (3w : 8 word); Word 4w]``;
