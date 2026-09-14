(* Direct HOL-EVAL probes for crepLang$var_cexp.
   Reference: cakeml/pancake/crepLangScript.sml:128-142. *)
load "bossLib";
load "preamble";
load "../crepLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "const"
  ``crepLang$var_cexp (crepLang$Const (7w : 8 word))``;
val _ = print_eval "var"
  ``crepLang$var_cexp (crepLang$Var 3 : 8 crepLang$exp)``;
val _ = print_eval "load_chain"
  ``crepLang$var_cexp
      (crepLang$Load (crepLang$Load32 (crepLang$Var 3)) : 8 crepLang$exp)``;
val _ = print_eval "glob"
  ``crepLang$var_cexp (crepLang$LoadGlob (4w : 5 word))``;
val _ = print_eval "op_flat"
  ``crepLang$var_cexp
      (crepLang$Op Add
        [crepLang$Var 3; crepLang$Const (7w : 8 word); crepLang$Var 4])``;
val _ = print_eval "cmp_concat"
  ``crepLang$var_cexp
      (crepLang$Cmp Equal (crepLang$Var 3) (crepLang$LoadByte (crepLang$Var 4)))``;
val _ = print_eval "base_top"
  ``(crepLang$var_cexp (crepLang$BaseAddr : 8 crepLang$exp),
     crepLang$var_cexp (crepLang$TopAddr : 8 crepLang$exp))``;
