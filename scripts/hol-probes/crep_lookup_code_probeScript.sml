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

(* Arity mismatch: one declared parameter but two supplied arguments. *)
val _ = print_eval "lookup_code_arity"
  ``crepSem$lookup_code ^code (strlit "id")
      [Word (7w : 8 word); Word (8w : 8 word)] 2``;

(* Duplicate declared parameters: ALL_DISTINCT [1;1] is false. *)
val code_dup = ``(FEMPTY |+ (strlit "dup", ([1;1], crepLang$Skip)))``;

val _ = print_eval "lookup_code_duplicate"
  ``crepSem$lookup_code ^code_dup (strlit "dup")
      [Word (7w : 8 word); Word (8w : 8 word)] 2``;
