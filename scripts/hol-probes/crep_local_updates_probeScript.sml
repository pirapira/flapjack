(*
  Direct HOL observations for crepSem$set_var_def / upd_locals_def /
  empty_locals_def.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:55-73.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;
val s0 = ``(^s with <|locals := FEMPTY |+ (2, Word (9w:8 word));
                       clock := 5; base_addr := 3w; top_addr := 100w|>)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "set_var_hit"
  ``FLOOKUP ((crepSem$set_var 1 (Word (7w:8 word)) (^s0)).locals) 1 =
      SOME (Word (7w:8 word))``;

val _ = print_eval "set_var_keeps_other"
  ``FLOOKUP ((crepSem$set_var 1 (Word (7w:8 word)) (^s0)).locals) 2 =
      SOME (Word (9w:8 word))``;

val _ = print_eval "upd_locals_replace"
  ``(case crepSem$upd_locals [(1,(Word (3w:8 word)))] (^s0) of s' =>
      (FLOOKUP s'.locals 1 = SOME (Word (3w:8 word))) /\
      (FLOOKUP s'.locals 2 = NONE))``;

val _ = print_eval "empty_locals_none"
  ``FLOOKUP ((crepSem$empty_locals (^s0)).locals) 2 = NONE``;

val _ = print_eval "set_var_fields_preserved"
  ``(case crepSem$set_var 1 (Word (7w:8 word)) (^s0) of s' =>
      (s'.clock = 5) /\ (s'.base_addr = 3w) /\ (s'.top_addr = 100w))``;

val _ = print_eval "empty_locals_fields_preserved"
  ``(case crepSem$empty_locals (^s0) of s' =>
      (s'.clock = 5) /\ (s'.memory = (^s0).memory))``;
