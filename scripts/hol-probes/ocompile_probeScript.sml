(* Direct HOL-EVAL fixture for crep_to_loop$ocompile.
   Reference: cakeml/pancake/crep_to_loopScript.sml:216. *)
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
    print (term_to_string (rconc th));
    print "\n"
  end

val ctxt =
  ``<| vars := (FEMPTY |+ (1,5)); funcs := FEMPTY;
      vmax := 0; target := RISC_V |>``;

val _ = print_eval "skip"
  ``crep_to_loop$ocompile ^ctxt LN
      (crepLang$Skip : 8 word crepLang$prog)``;
val _ = print_eval "dead_assign"
  ``crep_to_loop$ocompile ^ctxt LN
      (crepLang$Assign 1 (crepLang$Const (17w : 8 word)))``;
val _ = print_eval "return_const"
  ``crep_to_loop$ocompile ^ctxt LN
      (crepLang$Return [crepLang$Const (17w : 8 word)])``;
(* Keep a final one-line observation so regeneration retains the wrapped
   return_const term above. *)
val _ = print_eval "post_return_skip"
  ``crep_to_loop$ocompile ^ctxt LN
      (crepLang$Skip : 8 word crepLang$prog)``;
