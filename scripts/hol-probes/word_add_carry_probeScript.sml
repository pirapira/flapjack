(* Direct HOL-EVAL fixture for backend_common$word_add_carry.
   Reference: cakeml/compiler/backend/backend_commonScript.sml:170-176. *)
load "bossLib";
load "preamble";
load "backend_commonTheory";
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

val _ = print_eval "ordinary"
  ``let (res, co) = backend_common$word_add_carry (3w : 8 word) 4w 0w in
      (w2n res, w2n co)``;
val _ = print_eval "wrap"
  ``let (res, co) = backend_common$word_add_carry (255w : 8 word) 1w 0w in
      (w2n res, w2n co)``;
val _ = print_eval "nonzero_carry"
  ``let (res, co) = backend_common$word_add_carry (3w : 8 word) 4w 2w in
      (w2n res, w2n co)``;
val _ = print_eval "carry_overflow"
  ``let (res, co) = backend_common$word_add_carry (255w : 8 word) 0w 1w in
      (w2n res, w2n co)``;
