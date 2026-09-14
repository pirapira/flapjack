(* Direct HOL-EVAL fixture for pan_globals$compile_def. *)
load "bossLib";
load "preamble";
load "pan_globalsTheory";
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

val ctxt =
  ``((<| globals := FEMPTY |+ («g», (One, 8w));
      globals_size := 1w; max_globals_size := 16w |> ) :
      8 word pan_globals$context)``;
val _ = print_eval "local_assign"
  ``pan_globals$compile ^ctxt
      (panLang$Assign Local «x» (panLang$Const 7w) : 8 word panLang$prog)``;
val _ = print_eval "global_assign"
  ``pan_globals$compile ^ctxt
      (panLang$Assign Global «g» (panLang$Const 7w) : 8 word panLang$prog)``;
val _ = print_eval "missing_global_assign"
  ``pan_globals$compile ^ctxt
      (panLang$Assign Global «missing» (panLang$Const 7w) : 8 word panLang$prog)``;
val _ = print_eval "seq"
  ``pan_globals$compile ^ctxt
      (panLang$Seq panLang$Skip
        (panLang$Return (panLang$Const 7w)) : 8 word panLang$prog)``;
val _ = print_eval "return_global"
  ``pan_globals$compile ^ctxt
      (panLang$Return (panLang$Var Global «g») : 8 word panLang$prog)``;
