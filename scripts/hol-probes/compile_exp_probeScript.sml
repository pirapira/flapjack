(* Direct HOL-EVAL fixture for crep_to_loop$compile_exp_def. *)
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

val ctxt = ``(<| vars := FEMPTY; funcs := FEMPTY;
               vmax := 0; target := RISC_V |>)``;

val _ = print_eval "compile_exp_mul_three"
  ``crep_to_loop$compile_exp ^ctxt 10 LN
      (crepLang$Crepop crepLang$Mul
        [crepLang$Const 2w; crepLang$Const 3w; crepLang$Const 4w])``
