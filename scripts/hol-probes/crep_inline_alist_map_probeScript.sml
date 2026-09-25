(* Direct HOL-EVAL observations for the exact input-map construction used by
   compile_inl_top (`cakeml/pancake/crep_inlineScript.sml:259-269`).
   This pins the duplicate-first behavior of alist_to_fmap and DOMSUB. *)

load "bossLib";
load "preamble";
load "crep_inlineTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_inlineTheory;
open crepLangTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val body = ``(Skip : 8 crepLang$prog)``;
val bodyB = ``(Tick : 8 crepLang$prog)``;
val rows = ``[(«f», ([7], ^body)); («f», ([9], ^bodyB));
              («g», ([], ^body))]``;
val inline_map = ``alist_to_fmap ^rows``;

(* alist_to_fmap is FOLDR of map updates: the first input duplicate wins. *)
val _ = print_eval "alist_duplicate_first"
  ``FLOOKUP ^inline_map «f»``;
val _ = print_eval "alist_other_row"
  ``FLOOKUP ^inline_map «g»``;
val _ = print_eval "domsub_selected_f"
  ``FLOOKUP (^inline_map \\ «f») «f»``;
val _ = print_eval "input_rows_order"
  ``MAP FST ^rows``;
