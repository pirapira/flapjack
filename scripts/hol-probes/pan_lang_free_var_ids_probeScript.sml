(* Direct HOL-EVAL observations for panLang$free_var_ids.
   Reference: cakeml/pancake/panLangScript.sml:347-389. *)
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
  ``free_var_ids (Skip : (8 word) panLang$prog)``;
val _ = print_eval "assign_local"
  ``free_var_ids (Assign Local (strlit "v")
    (Var Local (strlit "x")))``;
val _ = print_eval "assign_global"
  ``free_var_ids (Assign Global (strlit "v")
    (Var Local (strlit "x")))``;
val _ = print_eval "declaration"
  ``free_var_ids (Dec (strlit "x") One (Var Local (strlit "e"))
    (Assign Local (strlit "x") (Var Local (strlit "x"))))``;
val _ = print_eval "conditional"
  ``free_var_ids (If (Var Local (strlit "g"))
    (Return (Var Local (strlit "p")))
    (Return (Var Local (strlit "q"))))``;
val _ = print_eval "ordinary_call"
  ``free_var_ids (Call NONE (strlit "f")
    [Var Local (strlit "a")])``;
val _ = print_eval "handled_call"
  ``free_var_ids
      (Call (SOME (NONE,
        SOME (strlit "E", strlit "h",
          Assign Local (strlit "z") (Var Local (strlit "q")))))
        (strlit "f") [Var Local (strlit "a")])``;
val _ = print_eval "dec_call"
  ``free_var_ids
      (DecCall (strlit "x") One (strlit "d")
        [Var Local (strlit "a")]
        (Return (Var Local (strlit "r"))))``;
