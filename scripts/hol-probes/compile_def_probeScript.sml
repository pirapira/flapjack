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

val _ = print_eval "missing_global"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Call
        (SOME (SOME (panLang$Global, «missing»), NONE)) «f» [])``;

val _ = print_eval "empty_one_global"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («empty_one», (panLang$One, []));
         funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Call
        (SOME (SOME (panLang$Global, «empty_one»), NONE)) «f» [])``;

val _ = print_eval "extra_names_global"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («extra_names», (panLang$One, [4; 5]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 5 |>
      (panLang$Call
        (SOME (SOME (panLang$Global, «extra_names»), NONE)) «f» [])``;

val _ = print_eval "missing_names_global"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («missing_names»,
          (panLang$Comb [panLang$One; panLang$One], [4]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 4 |>
      (panLang$Call
        (SOME (SOME (panLang$Global, «missing_names»), NONE)) «f» [])``;
