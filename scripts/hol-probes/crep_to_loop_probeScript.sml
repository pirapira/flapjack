(*
  Direct HOL outputs for crep_to_loop$compile (compile_def,
  crep_to_loopScript.sml:120).
*)
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

val _ = print_eval "compile_skip"
  ``crep_to_loop$compile
      <| vars := (FEMPTY |+ (1,5)); funcs := FEMPTY;
         vmax := 0; target := RISC_V |>
      LN (crepLang$Skip : 8 word crepLang$prog)``
val _ = print_eval "compile_raise"
  ``crep_to_loop$compile
      <| vars := (FEMPTY |+ (1,5)); funcs := FEMPTY;
         vmax := 0; target := RISC_V |>
      LN (crepLang$Raise (17w : 8 word))``
