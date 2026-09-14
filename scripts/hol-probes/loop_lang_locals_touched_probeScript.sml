(*
  Direct HOL-EVAL probes for Pancake loopLang$locals_touched.
  Reference: cakeml/pancake/loopLangScript.sml:77-88.
*)
load "bossLib";
load "preamble";
load "../loopLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "const"
  ``locals_touched (Const (7w : 32 word))``
val _ = print_eval "var"
  ``locals_touched (Var 3)``
val _ = print_eval "load_var"
  ``locals_touched (Load (Var 4))``
val _ = print_eval "op_nested"
  ``locals_touched (Op Add [Var 2; Load (Var 4); Const (7w : 32 word)])``
val _ = print_eval "base_addr"
  ``locals_touched BaseAddr``
