(*
  Direct HOL observations for the interaction-tree set_var_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:39-42.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val toNum = ``(\(x:8 v). case x of ValWord (w:8 word) => w2n w | _ => 0)``;
val s = ``(s:(8) pan_itreeSem$bstate)``;
val base1 =
  ``(^s with locals := (FEMPTY : (mlstring |-> 8 v)) |+
      (strlit "x", ValWord (5w:8 word)) |+
      (strlit "y", ValWord (7w:8 word)))``;
val base =
  ``(^base1 with globals := (FEMPTY : (mlstring |-> 8 v)) |+
      (strlit "g", ValWord (1w:8 word)))``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "set_var_new"
  ``OPTION_MAP ^toNum (FLOOKUP
      (set_var (strlit "z") (ValWord (9w:8 word)) ^base).locals
      (strlit "z"))``;
val _ = print_eval "set_var_overwrite"
  ``OPTION_MAP ^toNum (FLOOKUP
      (set_var (strlit "x") (ValWord (9w:8 word)) ^base).locals
      (strlit "x"))``;
val _ = print_eval "set_var_sibling"
  ``OPTION_MAP ^toNum (FLOOKUP
      (set_var (strlit "x") (ValWord (9w:8 word)) ^base).locals
      (strlit "y"))``;
val _ = print_eval "set_var_globals"
  ``OPTION_MAP ^toNum (FLOOKUP
      (set_var (strlit "x") (ValWord (9w:8 word)) ^base).globals
      (strlit "g"))``;
