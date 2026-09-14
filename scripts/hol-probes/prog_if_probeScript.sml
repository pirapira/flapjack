(* Direct HOL-EVAL fixture for crep_to_loop$prog_if_def. *)
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

val _ = print_eval "prog_if_basic"
  ``crep_to_loop$prog_if
      asm$NotEqual
      [loopLang$Skip] [loopLang$Tick]
      (loopLang$Const (2w : 8 word))
      (loopLang$Const (3w : 8 word))
      3 4
      (insert 1 () (insert 2 () LN))``
