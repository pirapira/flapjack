(*
  Direct HOL observations for itree_evaluate_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:582-594.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
load "panPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;
open panLangTheory;
open panSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;

fun print_eval label q =
  let
    val th = SIMP_CONV (srw_ss())
      [itree_evaluate_def, mrec_prog_triv, mrec_Return, eval_def,
       empty_locals_def, LET_THM,
       size_of_sh_with_ctxt_def, shape_of_def,
       Once itreeTauTheory.itree_unfold] q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "itree_evaluate_skip"
  ``case itree_evaluate (panLang$Skip,^s) of
      | itreeTau$Ret (NONE,s') => s' = ^s
      | _ => F``;

val _ = print_eval "itree_evaluate_break"
  ``case itree_evaluate (panLang$Break,^s) of
      | itreeTau$Ret (SOME Break,s') => s' = ^s
      | _ => F``;

val _ = print_eval "itree_evaluate_tick"
  ``case itree_evaluate (panLang$Tick,^s) of
      | itreeTau$Ret (NONE,s') => s' = ^s
      | _ => F``;
