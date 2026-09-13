(*
  Probe outputs for the original CakeML Pancake panSem definition set_var.
  This is intentionally a HOL script rather than a second implementation.
  The checked-in output is regenerated with scripts/hol-probes/regenerate.sh.

  Reference: cakeml/pancake/semantics/panSemScript.sml:398-401 (set_var_def).

  Words are fixed to 8 bits and results are printed as numeric w2n values.
*)
load "bossLib";
load "preamble";
load "semantics/panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val toNum = ``(\(x:8 v). case x of Val (Word (w:8 word)) => w2n w | RStruct _ => 0 | NStruct _ _ => 0)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val s = ``(s:(8,'ffi) panSem$state)``;
val base1 =
  ``(^s with locals := (FEMPTY : (mlstring |-> 8 v)) |+ (strlit "x", ValWord (5w:8 word)) |+ (strlit "y", ValWord (7w:8 word)))``;
val base =
  ``(^base1 with globals := (FEMPTY : (mlstring |-> 8 v)) |+ (strlit "g", ValWord (1w:8 word)))``;

val _ = print_eval "set_var_new"
  ``OPTION_MAP ^toNum (FLOOKUP (set_var (strlit "z") (ValWord (9w:8 word)) ^base).locals (strlit "z"))``
val _ = print_eval "set_var_overwrite"
  ``OPTION_MAP ^toNum (FLOOKUP (set_var (strlit "x") (ValWord (9w:8 word)) ^base).locals (strlit "x"))``
val _ = print_eval "set_var_other"
  ``OPTION_MAP ^toNum (FLOOKUP (set_var (strlit "x") (ValWord (9w:8 word)) ^base).locals (strlit "y"))``
val _ = print_eval "set_var_globals"
  ``OPTION_MAP ^toNum (FLOOKUP (set_var (strlit "x") (ValWord (9w:8 word)) ^base).globals (strlit "g"))``
val _ = print_eval "set_var_clock"
  ``(set_var (strlit "x") (ValWord (9w:8 word)) ^base).clock``
