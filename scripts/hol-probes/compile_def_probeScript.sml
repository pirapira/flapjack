(* Direct HOL-EVAL probes for pan_to_crep$compile (compile_def).
   Reference: cakeml/pancake/pan_to_crepScript.sml:139-305. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;
val _ = Globals.max_print_depth := 100;

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

(* Local-kind mirrors of the four Global cases above: Cake's assigned-call
   rule looks up the destination with `wrap_rt (FLOOKUP ctxt.vars rt)` and
   ignores the `rk` kind tag, so each pair must agree. *)

val _ = print_eval "missing_local"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Call
        (SOME (SOME (panLang$Local, «missing»), NONE)) «f» [])``;

val _ = print_eval "empty_one_local"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («empty_one», (panLang$One, []));
         funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Call
        (SOME (SOME (panLang$Local, «empty_one»), NONE)) «f» [])``;

val _ = print_eval "extra_names_local"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («extra_names», (panLang$One, [4; 5]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 5 |>
      (panLang$Call
        (SOME (SOME (panLang$Local, «extra_names»), NONE)) «f» [])``;

val _ = print_eval "missing_names_local"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («missing_names»,
          (panLang$Comb [panLang$One; panLang$One], [4]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 4 |>
      (panLang$Call
        (SOME (SOME (panLang$Local, «missing_names»), NONE)) «f» [])``;

val _ = print_eval "valid_local"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («pair»,
          (panLang$Comb [panLang$One; panLang$One], [0; 1]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 1 |>
      (panLang$Call
        (SOME (SOME (panLang$Local, «pair»), NONE)) «f» [])``;

val _ = print_eval "empty_struct_return"
  ``pan_to_crep$compile
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Return (panLang$RStruct []))``;

val _ = print_eval "finite_map_shadow_return"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («p», (panLang$One, [3]))
                 |+ («p», (panLang$One, [5]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 5 |>
      (panLang$Return (panLang$Var panLang$Local «p»))``;

(* The source freshness bound scans all var_cexp words, even though ExtCall
   requires each operand to have shape One and emits only its first word. *)
val _ = print_eval "extcall_high_tail"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («ptr1», (panLang$One, [4; 100]))
                 |+ («len1», (panLang$One, [5]))
                 |+ («ptr2», (panLang$One, [6]))
                 |+ («len2», (panLang$One, [7]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 100 |>
      (panLang$ExtCall «f»
        (panLang$Var panLang$Local «ptr1»)
        (panLang$Var panLang$Local «len1»)
        (panLang$Var panLang$Local «ptr2»)
        (panLang$Var panLang$Local «len2»))``;

val _ = print_eval "pair_load"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («p», (panLang$One, [0]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      (panLang$Return
        (panLang$Load (panLang$Comb [panLang$One; panLang$One])
          (panLang$Var panLang$Local «p»)) : 64 word panLang$prog)``;

val _ = print_eval "pair_store"
  ``pan_to_crep$compile
      <| vars := FEMPTY |+ («p», (panLang$One, [0]))
                 |+ («x», (panLang$One, [1]))
                 |+ («y», (panLang$One, [2]));
         funcs := FEMPTY; eids := FEMPTY; vmax := 2 |>
      (panLang$Store (panLang$Var panLang$Local «p»)
        (panLang$RStruct
          [panLang$Var panLang$Local «x»; panLang$Var panLang$Local «y»]) :
        64 word panLang$prog)``;

val _ = print_eval "fixed_stride64"
  ``(pan_to_crep$compile_exp
      <| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>
      panLang$BytesInWord : 64 word crepLang$exp list # panLang$shape)``;
