(* Direct HOL EVAL observations for Pancake lookup_code_def. *)
load "bossLib";
load "preamble";
load "../semantics/panSemTheory";
load "../semantics/panPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;
open panPropsTheory;

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

(* Conclusion row for panProps$lookup_code_wf_shape_invariant_step: the
   successful lookup's FUPDATE_LIST locals satisfy FEVERY is_wf_shape_v. *)
val _ = print_eval "lookup_code_wf_shape_invariant_step_success"
  ``case lookup_code
      (FEMPTY |+ (strlit "id",
        ([(strlit "x", One)], panLang$Skip, One)))
      (strlit "id") [ValWord (7w:8 word)] of
      | SOME (_, newlocals, _) =>
          FLOOKUP newlocals (strlit "x") = SOME (ValWord (7w:8 word)) /\
          is_wf_shape_v [] (ValWord (7w:8 word))
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
