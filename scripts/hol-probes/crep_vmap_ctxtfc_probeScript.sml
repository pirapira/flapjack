(* Direct HOL-EVAL observations for pan_to_crep$make_vmap (make_vmap_def,
   cakeml/pancake/pan_to_crepScript.sml:327) and the variable-map component of
   pan_to_crep$ctxt_fc (ctxt_fc_def, :25), the two parameter maps that HOL
   mk_ctxt_code_imp_code_rel identifies with gvs[ctxt_fc_def, make_vmap_def].

   Rows evaluate both maps on the ACTUAL parameter list [(«x»,One);(«y»,One)]
   and compare the looked-up (shape, slot-list) entries exactly (8-bit words so
   the exception-code map type is fixed). *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;
open panLangTheory;
open finite_mapTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val params = ``[(«x», panLang$One); («y», panLang$One)] :
  (mlstring # panLang$shape) list``;

val ns = ``GENLIST I (size_of_shape (Comb (MAP SND ^params)))``;
val ctxtvars = ``(FEMPTY : (mlstring, (panLang$shape # num list)) fmap) |++
  ZIP (MAP FST ^params, ZIP (MAP SND ^params, with_shape (MAP SND ^params) ^ns))``;

val _ = print_eval "vmap_x"
  ``FLOOKUP (pan_to_crep$make_vmap ^params) «x» = SOME (panLang$One, [0])``;
val _ = print_eval "vmap_y"
  ``FLOOKUP (pan_to_crep$make_vmap ^params) «y» = SOME (panLang$One, [1])``;
val _ = print_eval "vmap_absent"
  ``FLOOKUP (pan_to_crep$make_vmap ^params) «z» = NONE``;
val _ = print_eval "ns_offsets" ``^ns = [0; 1]``;
val _ = print_eval "ctxt_x"
  ``FLOOKUP ^ctxtvars «x» = SOME (panLang$One, [0])``;
val _ = print_eval "ctxt_y"
  ``FLOOKUP ^ctxtvars «y» = SOME (panLang$One, [1])``;
val _ = print_eval "vmap_eq_ctxt"
  ``(pan_to_crep$make_vmap ^params) = ^ctxtvars``;