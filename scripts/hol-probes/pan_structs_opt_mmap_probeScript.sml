(* Direct HOL-EVAL observations for pan_structsProof$opt_mmap_eq_some_el.
   Reference: cakeml/pancake/proofs/pan_structsProofScript.sml:19. *)
load "bossLib";
load "preamble";
load "../pan_structsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_structsTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "success"
  ``OPT_MMAP (\n. SOME (n + 1)) [3; 5] = SOME [4; 6]``;
val _ = print_eval "pointwise"
  ``LENGTH [3; 5] = LENGTH [4; 6] /\
    SOME (EL 0 [3; 5] + 1) = SOME (EL 0 [4; 6]) /\
    SOME (EL 1 [3; 5] + 1) = SOME (EL 1 [4; 6])``;
