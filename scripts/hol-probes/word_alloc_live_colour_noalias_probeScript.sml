(*
  Direct HOL observations for the live/write injectivity condition behind
  word_allocProof$colouring_ok on an assignment leaf.  The proof-side
  check_colouring_ok_alt input is the concrete clash set {write, live-after}.
*)

load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_allocTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end

val live_write = ``[sptree$fromAList [(1n,()); (2n,())]]``;
val live_after_write = ``[sptree$fromAList [(2n,()); (3n,())]]``;
val distinct = ``\n:num. if n = 1 then 8 else if n = 2 then 9 else n``;
val alias = ``\n:num. if n = 1 then 8 else if n = 2 then 8 else n``;
val live_after_distinct =
  ``\n:num. if n = 2 then 8 else if n = 3 then 9 else n``;
val live_after_alias =
  ``\n:num. if n = 2 then 8 else if n = 3 then 8 else n``;

val _ = print_eval "colour_ok_distinct_write_live"
  ``check_colouring_ok_alt ^distinct ^live_write``;
val _ = print_eval "colour_ok_alias_write_live"
  ``check_colouring_ok_alt ^alias ^live_write``;
val _ = print_eval "colour_ok_distinct_write_live_after"
  ``check_colouring_ok_alt ^live_after_distinct ^live_after_write``;
val _ = print_eval "colour_ok_alias_write_live_after"
  ``check_colouring_ok_alt ^live_after_alias ^live_after_write``;
