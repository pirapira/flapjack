(*
  Direct HOL observations for Pancake panLang$exp_ids.
  Reference: cakeml/pancake/panLangScript.sml:222-231.
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

val _ = print_eval "empty"
  ``exp_ids (Skip : (8 word) panLang$prog)``
val _ = print_eval "raise"
  ``exp_ids (Raise (strlit "E") (Const (7w : 8 word)))``
val _ = print_eval "sequence"
  ``exp_ids (Seq (Raise (strlit "E1") (Const (1w : 8 word)))
      (Raise (strlit "E2") (Const (2w : 8 word))))``
val _ = print_eval "dec"
  ``exp_ids (Dec (strlit "x") One (Const (0w : 8 word))
      (Raise (strlit "ED") (Const (3w : 8 word))))``
val _ = print_eval "conditional_loop"
  ``exp_ids (If (Const (0w : 8 word))
      (Raise (strlit "EI") (Const (4w : 8 word)))
      (While (Const (0w : 8 word))
        (Raise (strlit "EW") (Const (5w : 8 word)))))``
val _ = print_eval "call_handler"
  ``exp_ids (Call (SOME (NONE,
      SOME (strlit "EC", strlit "h",
        Seq (Raise (strlit "EH") (Const (6w : 8 word))) Skip)))
      (strlit "f") [])``
val _ = print_eval "fallback"
  ``exp_ids (Assign Local (strlit "x") (Const (9w : 8 word)))``
