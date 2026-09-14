(*
  Direct HOL-EVAL observations for Pancake panLang$var_exp and
  panLang$global_var_exp.
  Reference: cakeml/pancake/panLangScript.sml:253-293.
*)
load "bossLib";
load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "local_var"
  ``var_exp (Var Local (strlit "x"))``;
val _ = print_eval "global_var"
  ``global_var_exp (Var Global (strlit "g"))``;
val _ = print_eval "nested"
  ``var_exp
      (RStruct [Var Local (strlit "x");
                Var Global (strlit "g");
                NStruct (strlit "S")
                  [(strlit "field", Var Local (strlit "y"))];
                Load One (Var Global (strlit "addr"))])``;
val _ = print_eval "nested_global"
  ``global_var_exp
      (RStruct [Var Local (strlit "x");
                Var Global (strlit "g");
                NStruct (strlit "S")
                  [(strlit "field", Var Local (strlit "y"))];
                Load One (Var Global (strlit "addr"))])``;
