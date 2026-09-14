(*
  Direct HOL observations for h_prog_sh_mem_load_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:466-513.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;
val base = ``(^s with locals := (FEMPTY : (mlstring |-> 8 v)) |+
    (strlit "x", ValWord (0w:8 word))) with sh_memaddrs := {3w}``;
val s32 = ``(s:(32) pan_itreeSem$bstate)``;
val base32 = ``(^s32 with locals := (FEMPTY : (mlstring |-> 32 v)) |+
    (strlit "x", ValWord (0w:32 word))) with sh_memaddrs := {0w}``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "load_zero_width"
  ``case h_prog_sh_mem_load panLang$OpW panLang$Local (strlit "x")
      (panLang$Const (3w:8 word)) ^base of
      | itreeTau$Vis e k => SOME e
      | _ => NONE``;

val _ = print_eval "load_aligned_original"
  ``case h_prog_sh_mem_load panLang$Op8 panLang$Local (strlit "x")
      (panLang$Const (3w:32 word)) ^base32 of
      | itreeTau$Vis e k => SOME e
      | _ => NONE``;

val _ = print_eval "load_domain_error"
  ``case h_prog_sh_mem_load panLang$OpW panLang$Local (strlit "x")
      (panLang$Const (3w:8 word))
      (^base with sh_memaddrs := {}) of
      | itreeTau$Ret r => SOME r
      | _ => NONE``;

val _ = print_eval "load_return_value"
  ``case h_prog_sh_mem_load panLang$OpW panLang$Local (strlit "x")
      (panLang$Const (3w:8 word)) ^base of
      | itreeTau$Vis e k =>
          (case k (INL (INR [9w])) of
             | itreeTau$Ret (INR (r,s')) =>
                 FLOOKUP s'.locals (strlit "x") =
                   SOME (ValWord (9w:8 word))
             | _ => F)
      | _ => F``;

val _ = print_eval "load_mismatch_locals"
  ``case h_prog_sh_mem_load panLang$OpW panLang$Local (strlit "x")
      (panLang$Const (3w:8 word)) ^base of
      | itreeTau$Vis e k =>
          (case k (INL (INR [])) of
             | itreeTau$Ret (INR (r,s')) => FLOOKUP s'.locals (strlit "x")
             | _ => NONE)
      | _ => NONE``;

val _ = print_eval "load_final_locals"
  ``case h_prog_sh_mem_load panLang$OpW panLang$Local (strlit "x")
      (panLang$Const (3w:8 word)) ^base of
      | itreeTau$Vis e k =>
          (case k (INL (INL FFI_failed)) of
             | itreeTau$Ret (INR (r,s')) => FLOOKUP s'.locals (strlit "x")
             | _ => NONE)
      | _ => NONE``;
