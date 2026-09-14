(* Direct HOL-EVAL fixture for pan_structs$old_exp_shape_def. *)
load "bossLib";
load "preamble";
load "pan_structsTheory";
open bossLib;
open HolKernel Parse;
open preamble;

val ctxt =
  ``<| structs := [(«Pair», [(«left», One); («right», Comb [One; One])])];
      locals := [(«local», Comb [One; One])];
      globals := [(«global», Named «Pair»)] |>``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "local"
  ``pan_structs$old_exp_shape ^ctxt
      (panLang$Var panLang$Local «local»)``;
val _ = print_eval "global"
  ``pan_structs$old_exp_shape ^ctxt
      (panLang$Var panLang$Global «global»)``;
val _ = print_eval "rstruct"
  ``pan_structs$old_exp_shape ^ctxt
      (panLang$RStruct [panLang$Const (1w : 8 word);
                       panLang$Const (2w : 8 word)])``;
val _ = print_eval "rfield_hit"
  ``pan_structs$old_exp_shape ^ctxt
      (panLang$RField 1
        (panLang$RStruct [panLang$Const (1w : 8 word);
                         panLang$Const (2w : 8 word)]))``;
val _ = print_eval "rfield_miss"
  ``pan_structs$old_exp_shape ^ctxt
      (panLang$RField 4
        (panLang$RStruct [panLang$Const (1w : 8 word)]))``;
val _ = print_eval "nstruct"
  ``pan_structs$old_exp_shape ^ctxt
      (panLang$NStruct «Pair» [])``;
val _ = print_eval "nfield_hit"
  ``pan_structs$old_exp_shape ^ctxt
      (panLang$NField «right» (panLang$NStruct «Pair» []))``;
val _ = print_eval "nfield_miss"
  ``pan_structs$old_exp_shape ^ctxt
      (panLang$NField «missing» (panLang$NStruct «Pair» []))``;
val _ = print_eval "load"
  ``pan_structs$old_exp_shape ^ctxt
      (panLang$Load (Comb [One; One]) (panLang$Const (0w : 8 word)))``;
val _ = print_eval "fallback"
  ``pan_structs$old_exp_shape ^ctxt
      (panLang$Const (0w : 8 word))``;
