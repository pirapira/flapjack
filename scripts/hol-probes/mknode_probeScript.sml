(* Direct HOL-EVAL fixture for parser$panPEG$mknode_def. *)
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
  ``mknode (INL ProgNT) []``;
val _ = print_eval "single"
  ``mknode (INL ProgNT)
      [Lf (TOK (KeywordT SkipK), Locs (POSN 2 3) (POSN 2 7))]``;
val _ = print_eval "multiple"
  ``mknode (INL ProgNT)
      [Lf (TOK (KeywordT SkipK), Locs (POSN 2 3) (POSN 2 7));
       Lf (TOK (KeywordT RetK), Locs (POSN 2 9) (POSN 2 12))]``;
