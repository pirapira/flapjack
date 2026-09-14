(*
  Direct HOL observations for h_prog_store_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:277-285.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;
val base = ``(^s with memory := (3w =+ panSem$Word (0w:8 word))
    (λ_. panSem$Word (0w:8 word))) with memaddrs := {3w}``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "store_success"
  ``case h_prog_store (panLang$Const (3w:8 word))
      (panLang$Const (7w:8 word)) ^base of
      | itreeTau$Ret (INR (NONE,s')) =>
          s'.memory 3w = panSem$Word (7w:8 word)
      | _ => F``;

val _ = print_eval "store_domain_error"
  ``case h_prog_store (panLang$Const (4w:8 word))
      (panLang$Const (7w:8 word)) ^base of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;

val _ = print_eval "store_invalid_address"
  ``case h_prog_store
      (panLang$Var panLang$Local (strlit "missing"))
      (panLang$Const (7w:8 word)) (^base with locals := FEMPTY) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;

val _ = print_eval "store_invalid_value"
  ``case h_prog_store (panLang$Const (3w:8 word))
      (panLang$Var panLang$Local (strlit "missing")) (^base with locals := FEMPTY) of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;
