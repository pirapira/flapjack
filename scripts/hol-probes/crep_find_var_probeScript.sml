(* Direct HOL outputs for crep_to_loop$find_var (find_var_def, line 20). *)
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

val _ = print_eval "find_var_hit"
  ``crep_to_loop$find_var
      (<| vars := (FEMPTY |+ (1,5)); funcs := FEMPTY;
          vmax := 0; target := RISC_V |>) 1``
val _ = print_eval "find_var_miss"
  ``crep_to_loop$find_var
      (<| vars := (FEMPTY |+ (1,5)); funcs := FEMPTY;
          vmax := 0; target := RISC_V |>) 2``
