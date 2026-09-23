(* Direct HOL-EVAL fixture for pan_structs$compile_exp_def. *)
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

val _ = print_eval "rstruct"
  ``pan_structs$compile_exp ^ctxt
      (panLang$RStruct [panLang$Const (1w : 8 word);
                       panLang$Const (2w : 8 word)])``;
val _ = print_eval "rfield"
  ``pan_structs$compile_exp ^ctxt
      (panLang$RField 1
        (panLang$RStruct [panLang$Const (1w : 8 word);
                         panLang$Const (2w : 8 word)]))``;
val _ = print_eval "nstruct"
  ``pan_structs$compile_exp ^ctxt
      (panLang$NStruct «Pair»
        [(«right», panLang$Const (2w : 8 word));
         («left», panLang$Const (1w : 8 word))])``;
val _ = print_eval "nfield"
  ``pan_structs$compile_exp ^ctxt
      (panLang$NField «right» (panLang$NStruct «Pair» []))``;
val _ = print_eval "load"
  ``pan_structs$compile_exp ^ctxt
      (panLang$Load (Named «Pair») (panLang$Const (0w : 8 word)))``;
val _ = print_eval "load32"
  ``pan_structs$compile_exp ^ctxt
      (panLang$Load32 (panLang$Const (0w : 8 word)))``;
val _ = print_eval "loadbyte"
  ``pan_structs$compile_exp ^ctxt
      (panLang$LoadByte (panLang$Const (0w : 8 word)))``;
val _ = print_eval "fallback"
  ``pan_structs$compile_exp ^ctxt
      (panLang$Const (0w : 8 word))``;
val _ = print_eval "list_map"
  ``pan_structs$compile_exps ^ctxt
      [panLang$NStruct «Pair»
        [(«right», panLang$Const (2w : 8 word));
         («left», panLang$Const (1w : 8 word))];
       panLang$Const (3w : 8 word)] =
    MAP (pan_structs$compile_exp ^ctxt)
      [panLang$NStruct «Pair»
        [(«right», panLang$Const (2w : 8 word));
         («left», panLang$Const (1w : 8 word))];
       panLang$Const (3w : 8 word)]``;
val _ = print_eval "old_shapes_map"
  ``pan_structs$old_exp_shapes ^ctxt
      [panLang$Var Local «local»;
       panLang$Var Global «global»;
       panLang$NStruct «Pair» [];
       panLang$RStruct
         [panLang$Const (2w : 8 word);
          panLang$Var Global «global»;
          panLang$Var Local «local»]] =
    MAP (pan_structs$old_exp_shape ^ctxt)
      [panLang$Var Local «local»;
       panLang$Var Global «global»;
       panLang$NStruct «Pair» [];
       panLang$RStruct
         [panLang$Const (2w : 8 word);
          panLang$Var Global «global»;
          panLang$Var Local «local»]]``;
