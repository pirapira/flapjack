(* Direct HOL EVAL rows for crep_to_loopScript.sml:make_funcs_def. *)
load "bossLib";
load "preamble";
load "mlstringTheory";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open mlstringTheory;
open crep_to_loopProofTheory;

fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

val prog = ``[(«f», ([1;2] : num list), (crepLang$Skip : 8 crepLang$prog));
              («g», ([] : num list), (crepLang$Skip : 8 crepLang$prog))]``;

val dup = ``[(«f», ([1] : num list), (crepLang$Skip : 8 crepLang$prog));
             («f», ([1;2;3] : num list), (crepLang$Skip : 8 crepLang$prog))]``;

val _ = print_eval "mkf_f"
  ``case FLOOKUP (make_funcs ^prog) «f» of
      SOME (n,m) => (n = 64) /\ (m = 2) | NONE => F``;

val _ = print_eval "mkf_g"
  ``case FLOOKUP (make_funcs ^prog) «g» of
      SOME (n,m) => (n = 65) /\ (m = 0) | NONE => F``;

val _ = print_eval "mkf_absent"
  ``FLOOKUP (make_funcs ^prog) «h» = NONE``;

val _ = print_eval "mkf_dup_first"
  ``case FLOOKUP (make_funcs ^dup) «f» of
      SOME (n,m) => (n = 64) /\ (m = 1) | NONE => F``;