(* Direct HOL-EVAL fixture for pan_globals$compile_exp_def. *)
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
val _ = print_eval "local"
  ``pan_globals$compile_exp ^ctxt
      (panLang$Var Local «x» : 8 word panLang$exp)``;
val _ = print_eval "global_hit"
  ``pan_globals$compile_exp ^ctxt
      (panLang$Var Global «g» : 8 word panLang$exp)``;
val _ = print_eval "global_miss"
  ``pan_globals$compile_exp ^ctxt
      (panLang$Var Global «missing» : 8 word panLang$exp)``;
val _ = print_eval "top_addr"
  ``pan_globals$compile_exp ^ctxt
      (panLang$TopAddr : 8 word panLang$exp)``;
val _ = print_eval "nested"
  ``pan_globals$compile_exp ^ctxt
      (panLang$Op Add
        [panLang$Var Global «g»; panLang$TopAddr] : 8 word panLang$exp)``;
