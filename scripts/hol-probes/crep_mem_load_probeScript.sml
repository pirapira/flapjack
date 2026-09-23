(*
  Direct HOL observations for the crepSem$state.memory total word_lab shape.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:24-26 (state field
  `memory : 'a word -> 'a word_lab`), :48-51 (mem_load_def) and :93-96
  (`eval s (Load addr) = ... mem_load w s`).  Memory is a total function of
  addresses; `memaddrs` is the separate guard.  A valid load returns the
  wrapped `Word` cell, an address outside `memaddrs` returns NONE.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;
val s0 = ``(^s with <|
    memory := (\(_ : 8 word). Word (7w:8 word));
    memaddrs := {(0w:8 word)} |>)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "mem_load_valid"
  ``crepSem$mem_load (0w:8 word) ^s0``;

val _ = print_eval "mem_load_invalid"
  ``crepSem$mem_load (1w:8 word) ^s0``;

val _ = print_eval "mem_load_other_valid"
  ``crepSem$mem_load (0w:8 word) (^s0 with memaddrs := {(0w:8 word); (2w:8 word)})``;

val _ = print_eval "eval_load_valid"
  ``crepSem$eval ^s0 (crepLang$Load (crepLang$Const (0w:8 word)))``;

val _ = print_eval "eval_load_invalid"
  ``crepSem$eval ^s0 (crepLang$Load (crepLang$Const (1w:8 word)))``;
