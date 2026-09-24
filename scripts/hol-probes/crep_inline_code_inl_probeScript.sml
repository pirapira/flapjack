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
val bodyB = ``(Dec 9 (Const (3w:8 word)) Skip) : 8 crepLang$prog``;
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

(* Representative finite-map cases, mirroring the unique-key Lean
   `CrepInlineFmap` representation (flapjack-pxn.18.5.5.7). *)

(* Duplicate key: HOL `|+` overwrites, so `FLOOKUP` returns the last binding
   `([9], bodyB)` and `inline_prog` inlines `bodyB`, never `body`. *)
val inl_fs_dup =
  ``((FEMPTY |+ («f», ([7], ^body)) |+ («f», ([9], ^bodyB))) :
      (mlstring, num list # 8 crepLang$prog) fmap)``;
val _ = print_eval "lookup_dup_f" ``FLOOKUP ^inl_fs_dup «f»``;
val _ = print_eval "inline_dup_call"
  ``inline_prog ^inl_fs_dup ((Call NONE «f» []) : 8 crepLang$prog)``;

(* DOMSUB: the callee body calls `f` again, and inline_prog removes `f` from
   the map before recursing, so the nested call is left untouched. *)
val inl_fs_nested =
  ``((FEMPTY |+ («f», ([], (Call NONE «f» [])))) :
      (mlstring, num list # 8 crepLang$prog) fmap)``;
val _ = print_eval "inline_nested_call"
  ``inline_prog ^inl_fs_nested ((Call NONE «f» []) : 8 crepLang$prog)``;

(* Argument loading: `arg_load` with `args = [Const 5w]` and
   `args_vname = [7]` produces temporary variables via GENLIST. *)
val inl_fs_arg =
  ``((FEMPTY |+ («f», ([7], ^body))) :
      (mlstring, num list # 8 crepLang$prog) fmap)``;
val _ = print_eval "inline_arg_call"
  ``inline_prog ^inl_fs_arg
      ((Call NONE «f» [Const (5w:8 word)]) : 8 crepLang$prog)``;
(* Skip is left unchanged by the inline pass. *)
val _ = print_eval "skip_identity"
  ``inline_prog ^inl_fs ((Skip) : 8 crepLang$prog) = ((Skip) : 8 crepLang$prog)``;
