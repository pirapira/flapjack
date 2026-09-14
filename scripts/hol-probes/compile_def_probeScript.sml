(* Direct HOL-EVAL probes for pan_to_crep$compile (compile_def).
   Reference: cakeml/pancake/pan_to_crepScript.sml:139-305. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "return"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (Return (Const (7w : 8 word)))``;
