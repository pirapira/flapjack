(*
  Direct HOL observations for mrec_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:173-190.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val identity_rh =
  ``(λ(_:unit). Ret () : (unit,unit+ev,unit) itree)``;

val tau_rh =
  ``(λ(_:unit). Tau (Ret ()) : (unit,unit+ev,unit) itree)``;

fun print_eval label q =
  let
    val th = SIMP_CONV (srw_ss())
      [mrec_def, Once itreeTauTheory.itree_iter_thm,
       itreeTauTheory.itree_bind_thm] q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "mrec_ret"
  ``case mrec ^identity_rh (Ret ()) of
      | Ret () => T
      | _ => F``;

val _ = print_eval "mrec_tau"
  ``case mrec ^identity_rh (Tau (Ret ())) of
      | Tau (Ret ()) => T
      | _ => F``;

val _ = print_eval "mrec_internal"
  ``case mrec ^identity_rh
      (Vis (INL ()) (λ(_:unit). Ret ())) of
      | Tau (Ret ()) => T
      | _ => F``;

val _ = print_eval "mrec_internal_intermediate"
  ``case mrec ^tau_rh
      (Vis (INL ()) (λ(_:unit). Ret ())) of
      | Tau (Tau (Ret ())) => T
      | _ => F``;

val _ = print_eval "mrec_external"
  ``case mrec ^identity_rh
      (Vis (INR (ffi$ExtCall «foo», [], [1w:8 word]))
        (λ(_:unit). Ret ())) of
      | Vis (ffi$ExtCall «foo», [], [1w:8 word]) k =>
          (case k () of
             | Tau (Ret ()) => T
             | _ => F)
      | _ => F``;
