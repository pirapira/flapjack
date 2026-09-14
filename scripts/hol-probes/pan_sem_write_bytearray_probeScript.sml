(*
  Direct HOL observations for panSem$write_bytearray_def.
  Reference: cakeml/pancake/semantics/panSemScript.sml:309-316.
*)
load "bossLib";
load "preamble";
load "panSemTheory";
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

val initial_memory =
  ``(\a:64 word. if a = 8w then Word (0w:64 word) else Word (1w:64 word))``;

val _ = print_eval "write_empty"
  ``(write_bytearray (8w:64 word) [] ^initial_memory {8w} F) 8w``;

val _ = print_eval "write_hit"
  ``(write_bytearray (8w:64 word) [(0xaaw:8 word)] ^initial_memory {8w} F) 8w``;

val _ = print_eval "write_miss"
  ``(write_bytearray (8w:64 word) [(0xaaw:8 word)] ^initial_memory {16w} F) 8w``;
