(*
  Direct HOL observation for `evaluate_replicate_const`
  (cakeml/pancake/proofs/pan_to_crepProofScript.sml:3051-3054):
    !n s. OPT_MMAP (eval s) (REPLICATE n (Const 0w)) = SOME (REPLICATE n (Word 0w))
  The target `crepSem$eval` of a constant returns the `word_lab` wrapper `Word w`
  (crepSemScript.sml:90-91), so a list of constants evaluates to a list of
  wrapped words.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;
val s0 = ``(^s with locals := FEMPTY)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "replicate_const_one"
  ``OPT_MMAP (crepSem$eval ^s0) (REPLICATE 1 (crepLang$Const (0w:8 word)))``;

val _ = print_eval "replicate_const_three"
  ``OPT_MMAP (crepSem$eval ^s0) (REPLICATE 3 (crepLang$Const (0w:8 word)))``;

val _ = print_eval "replicate_const_empty"
  ``OPT_MMAP (crepSem$eval ^s0) (REPLICATE 0 (crepLang$Const (0w:8 word)))``;

val _ = print_eval "replicate_const_nonzero"
  ``OPT_MMAP (crepSem$eval ^s0) (REPLICATE 2 (crepLang$Const (9w:8 word)))``;
