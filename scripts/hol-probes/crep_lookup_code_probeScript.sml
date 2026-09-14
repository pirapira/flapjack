(* Direct HOL-EVAL probes for CakeML Pancake crepSem lookup_code_def. *)
(* Reference: cakeml/pancake/semantics/crepSemScript.sml:76-84. *)
load "bossLib";
load "preamble";
load "crepSemTheory";
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

val code = ``(FEMPTY |+ (strlit "id", ([1], crepLang$Skip)))``;

val _ = print_eval "lookup_code_valid"
  ``case crepSem$lookup_code ^code (strlit "id")
      [Word (7w : 8 word)] 1 of
      | SOME (prog, locals) => FLOOKUP locals 1
      | NONE => NONE``;

val _ = print_eval "lookup_code_missing"
  ``crepSem$lookup_code ^code (strlit "missing") [] 0``;
