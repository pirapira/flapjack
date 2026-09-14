(*
  Direct HOL observations for panSem$set_kvar_def.
  Reference: cakeml/pancake/semantics/panSemScript.sml:408-414.
*)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val s = ``(s:(8,unit) panSem$state)``;
val base = ``(^s with <|locals := FEMPTY; globals := FEMPTY|>)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "set_kvar_local"
  ``FLOOKUP (panSem$set_kvar panLang$Local (strlit "x")
      (ValWord (5w:8 word)) ^base).locals (strlit "x") =
      SOME (ValWord 5w)``;

val _ = print_eval "set_kvar_global"
  ``FLOOKUP (panSem$set_kvar panLang$Global (strlit "g")
      (ValWord (5w:8 word)) ^base).globals (strlit "g") =
      SOME (ValWord 5w)``;

val _ = print_eval "set_kvar_local_globals"
  ``FLOOKUP (panSem$set_kvar panLang$Local (strlit "x")
      (ValWord (5w:8 word)) ^base).globals (strlit "g") = NONE``;

val _ = print_eval "set_kvar_global_locals"
  ``FLOOKUP (panSem$set_kvar panLang$Global (strlit "g")
      (ValWord (5w:8 word)) ^base).locals (strlit "x") = NONE``;
