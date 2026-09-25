(* Direct HOL-EVAL probes for CakeML Pancake crepProps assigned_vars /
   var_exp load_shape lemmas (crepPropsScript.sml:215, :390, :400, :429,
   :439). *)
load "bossLib";
load "preamble";
load "crepLangTheory";
load "crepPropsTheory";
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
  end

val _ = print_eval "avnda"
  ``assigned_vars (nested_decs [1;2] [Const (0w:64 word); Var 1] Skip)``
val _ = print_eval "afvnda"
  ``assigned_free_vars
      (nested_decs [1;2] [Const (0w:64 word); Var 1] (Assign 9 (Var 3)))``
val _ = print_eval "avsse"
  ``assigned_vars
      (nested_seq
         (stores (Var 0) [Const (5w:64 word); Const (6w:64 word)]
            (0w:64 word)))``
val _ = print_eval "afvsse"
  ``assigned_free_vars
      (nested_seq
         (stores (Var 0) [Const (5w:64 word); Const (6w:64 word)]
            (0w:64 word)))``
val _ = print_eval "vels"
  ``MAP var_cexp (load_shape (0w:64 word) 2 (Var 3))``
