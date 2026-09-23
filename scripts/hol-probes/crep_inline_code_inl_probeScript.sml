(* Direct HOL-EVAL observations for the `inline_prog` term that appears in
   `crep_inlineProofScript.sml:1504` `code_inl_rel_def`.

   References:
     cakeml/pancake/crep_inlineScript.sml:203-249: inline_prog
     cakeml/pancake/crep_inlineScript.sml:59: arg_load
     cakeml/pancake/crep_inlineScript.sml:171: inline_tail *)

load "bossLib";
load "preamble";
load "crep_inlineTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_inlineTheory;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val body = ``(Dec 1 (Const (1w:8 word)) Skip) : 8 crepLang$prog``;
val inl_fs =
  ``((FEMPTY |+ («f», ([7], ^body))) :
      (mlstring, num list # 8 crepLang$prog) fmap)``;

val _ = print_eval "flookup_f" ``FLOOKUP ^inl_fs «f»``;
val _ = print_eval "inlined_call"
  ``inline_prog ^inl_fs ((Call NONE «f» []) : 8 crepLang$prog)``;
val _ = print_eval "no_match_call"
  ``inline_prog ^inl_fs ((Call NONE «g» []) : 8 crepLang$prog)``;
val _ = print_eval "handler_call_untouched"
  ``inline_prog ^inl_fs
      ((Call (SOME ([1], SOME ((2w:8 word), Skip))) «f» []) : 8 crepLang$prog)``;