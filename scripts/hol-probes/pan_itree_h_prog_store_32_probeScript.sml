(*
  Direct HOL observations for h_prog_store_32_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:297-306.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(64) pan_itreeSem$bstate)``;
val base = ``((^s with be := F) with memory := (8w =+ panSem$Word (0w:64 word))
    (λ_. panSem$Word (0w:64 word))) with memaddrs := {8w}``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "store_32_success"
  ``case h_prog_store_32 (panLang$Const (8w:64 word))
      (panLang$Const (0x11223344w:64 word)) ^base of
      | itreeTau$Ret (INR (NONE,s')) =>
          s'.memory 8w = panSem$Word (0x11223344w:64 word)
      | _ => F``;

val _ = print_eval "store_32_domain_error"
  ``case h_prog_store_32 (panLang$Const (4w:64 word))
      (panLang$Const (0x11223344w:64 word)) ^base of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;
