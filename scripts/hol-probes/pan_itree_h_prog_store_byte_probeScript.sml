(*
  Direct HOL observations for h_prog_store_byte_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:287-296.
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

val _ = print_eval "store_byte_success"
  ``case h_prog_store_byte (panLang$Const (3w:8 word))
      (panLang$Const (7w:8 word)) ^base of
      | itreeTau$Ret (INR (NONE,s')) =>
          s'.memory 3w = panSem$Word (7w:8 word)
      | _ => F``;

val _ = print_eval "store_byte_domain_error"
  ``case h_prog_store_byte (panLang$Const (4w:8 word))
      (panLang$Const (7w:8 word)) ^base of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;
