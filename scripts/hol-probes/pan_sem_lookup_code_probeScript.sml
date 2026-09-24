(* Direct HOL EVAL observations for Pancake lookup_code_def. *)
load "bossLib";
load "preamble";
load "../semantics/panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "lookup_code_nonempty_success"
  ``case lookup_code
      (FEMPTY |+ (strlit "id",
        ([(strlit "x", One)], panLang$Skip, One)))
      (strlit "id") [Val (Word (7w:8 word))] of
      | SOME (body, locals, return_shape) =>
          body = panLang$Skip /\ return_shape = One /\
          FLOOKUP locals (strlit "x") = SOME (Val (Word (7w:8 word)))
      | NONE => F``;

val _ = print_eval "lookup_code_missing_function"
  ``case lookup_code
      (FEMPTY |+ (strlit "other",
        ([(strlit "x", One)], panLang$Skip, One)))
      (strlit "missing") [] of
      | NONE => T
      | SOME _ => F``;

val _ = print_eval "lookup_code_wrong_arity"
  ``case lookup_code
      (FEMPTY |+ (strlit "id",
        ([(strlit "x", One)], panLang$Skip, One)))
      (strlit "id") [] of
      | NONE => T
      | SOME _ => F``;

val _ = print_eval "lookup_code_wrong_shape"
  ``case lookup_code
      (FEMPTY |+ (strlit "id",
        ([(strlit "x", One)], panLang$Skip, One)))
      (strlit "id") [RStruct []] of
      | NONE => T
      | SOME _ => F``;

val _ = print_eval "lookup_code_duplicate_formals"
  ``case lookup_code
      (FEMPTY |+ (strlit "dup",
        ([(strlit "x", One); (strlit "x", One)], panLang$Skip, One)))
      (strlit "dup") [Val (Word (7w:8 word)); Val (Word (8w:8 word))] of
      | NONE => T
      | SOME _ => F``;
