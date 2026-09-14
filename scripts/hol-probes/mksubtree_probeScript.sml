(* Direct HOL-EVAL fixture for parser$panPEG$mksubtree_def. *)
load "bossLib";
load "preamble";
load "panPEGTheory";
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

val _ = print_eval "empty"
  ``mksubtree (INL ProgNT) []``;
val _ = print_eval "child"
  ``mksubtree (INL ProgNT)
      [Lf (TOK (KeywordT SkipK), Locs (POSN 3 2) (POSN 3 6))]``;
