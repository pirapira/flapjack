(* Direct HOL-EVAL probes for pan_to_crepProof$globals_lookup_def. *)
load "bossLib";
load "preamble";
load "pan_to_crepProofTheory";
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

val _ = print_eval "lookup_success"
  ``pan_to_crepProof$globals_lookup
      (((ARB:((8),unit) crepSem$state) with
          globals := FEMPTY |+ (0w : 5 word, Word (7w : 8 word))))
      (ValWord (7w : 8 word))``;
val _ = print_eval "lookup_missing"
  ``pan_to_crepProof$globals_lookup
      (((ARB:((8),unit) crepSem$state) with globals := FEMPTY))
      (ValWord (7w : 8 word))``;
val _ = print_eval "lookup_struct"
  ``pan_to_crepProof$globals_lookup
      (((ARB:((8),unit) crepSem$state) with
          globals := FEMPTY |+ (0w : 5 word, Word (7w : 8 word))
            |+ (1w : 5 word, Word (8w : 8 word))))
      (RStruct [ValWord (3w : 8 word); ValWord (4w : 8 word)])``;
