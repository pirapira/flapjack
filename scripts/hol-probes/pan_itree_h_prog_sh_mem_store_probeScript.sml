(*
  Direct HOL observations for h_prog_sh_mem_store_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:513-558.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;
val s32 = ``(s:(32) pan_itreeSem$bstate)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "store_zero_width"
  ``case h_prog_sh_mem_store panLang$OpW
      (panLang$Const (3w:8 word)) (panLang$Const (7w:8 word))
      (^s with sh_memaddrs := {3w}) of
      | itreeTau$Vis e k => SOME e
      | _ => NONE``;

val _ = print_eval "store_aligned_original"
  ``case h_prog_sh_mem_store panLang$Op8
      (panLang$Const (3w:32 word)) (panLang$Const (171w:32 word))
      (^s32 with sh_memaddrs := {0w}) of
      | itreeTau$Vis e k => SOME e
      | _ => NONE``;

val _ = print_eval "store_domain_error"
  ``case h_prog_sh_mem_store panLang$OpW
      (panLang$Const (3w:8 word)) (panLang$Const (7w:8 word))
      (^s with sh_memaddrs := {}) of
      | itreeTau$Ret r => SOME r
      | _ => NONE``;
