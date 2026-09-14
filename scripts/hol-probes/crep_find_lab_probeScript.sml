(* Direct HOL outputs for crep_to_loop$find_lab (find_lab_def, line 27). *)
load "bossLib";
load "preamble";
load "crep_to_loopTheory";
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
  end

val _ = print_eval "find_lab_hit"
  ``crep_to_loop$find_lab
      (<| vars := FEMPTY;
          funcs := (FEMPTY |+ («f»,(64,2)));
          vmax := 0; target := RISC_V |>) «f»``
val _ = print_eval "find_lab_miss"
  ``crep_to_loop$find_lab
      (<| vars := FEMPTY;
          funcs := (FEMPTY |+ («f»,(64,2)));
          vmax := 0; target := RISC_V |>) «missing»``
