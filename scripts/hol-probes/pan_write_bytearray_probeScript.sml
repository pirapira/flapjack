(*
  Direct HOL observations for the active write_bytearray_def.
  Reference: cakeml/pancake/semantics/panSemScript.sml:300-314.
*)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val base = ``(((4w:8 word) =+ Word (0w:8 word))
    (((3w:8 word) =+ Word (0w:8 word))
      (λ_:(8 word). Word (0w:8 word))))``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "write_bytearray_two_cells"
  ``let m = write_bytearray (3w:8 word) [7w; 8w] ^base {3w; 4w} F in
      (m 3w = Word 7w) /\ (m 4w = Word 8w)``;

val _ = print_eval "write_bytearray_failed_tail"
  ``let m = write_bytearray (3w:8 word) [7w; 8w] ^base {3w} F in
      (m 3w = Word 7w) /\ (m 4w = Word 0w)``;
