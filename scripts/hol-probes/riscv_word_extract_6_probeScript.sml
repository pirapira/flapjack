(*
  Direct HOL observations for riscv_targetProof$word_extract_6 at its lower
  boundary and the largest 64-bit value covered by the premise.
*)

load "bossLib";
load "preamble";
load "riscv_targetTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open riscv_targetTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end

val _ = print_eval "word_extract_6_zero"
  ``(0w:word64) <+ 64w ==> ((5 >< 0) (0w:word64)):word6 = (w2w (0w:word64):word6)``;
val _ = print_eval "word_extract_6_63"
  ``(63w:word64) <+ 64w ==> ((5 >< 0) (63w:word64)):word6 = (w2w (63w:word64):word6)``;
val _ = print_eval "word_extract_6_64_premise"
  ``(64w:word64) <+ 64w``;
