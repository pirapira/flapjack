(* Direct HOL-EVAL observations for pan_to_crep$get_eids_from_decls
   (get_eids_from_decls_def, cakeml/pancake/pan_to_crepScript.sml:356), the
   definition unfolded by HOL get_eids_imp_excp_rel
   (pan_to_crepProofScript.sml:4656).

   The rows evaluate get_eids_from_decls on a concrete declaration list with two
   exception declarations and compare the looked-up exception-code words
   exactly (8-bit words so the index-to-word conversion is visible). *)
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

val decls = ``[panLang$ExnDecl «E» panLang$One;
                panLang$ExnDecl «F» panLang$One] : 8 panLang$decl list``;

val _ = print_eval "eids_present"
  ``FLOOKUP (pan_to_crep$get_eids_from_decls ^decls) «E» = SOME (0w:8 word)``;
val _ = print_eval "eids_second"
  ``FLOOKUP (pan_to_crep$get_eids_from_decls ^decls) «F» = SOME (1w:8 word)``;
val _ = print_eval "eids_absent"
  ``FLOOKUP (pan_to_crep$get_eids_from_decls ^decls) «G» = NONE``;
val _ = print_eval "eids_codes_distinct"
  ``(FLOOKUP (pan_to_crep$get_eids_from_decls ^decls) «E») <>
    (FLOOKUP (pan_to_crep$get_eids_from_decls ^decls) «F»)``;