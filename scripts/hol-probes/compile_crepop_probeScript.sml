(* Direct HOL-EVAL fixture for crep_to_loop$compile_crepop_def. *)
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

val _ = print_eval "compile_crepop_mul_riscv"
  ``crep_to_loop$compile_crepop
      crepLang$Mul RISC_V 2 3 4 LN``
