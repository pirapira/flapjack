(* Direct HOL-EVAL probes for CakeML Pancake panLang size_of_sh_with_ctxt_eq
   (panPropsScript.sml:184): a shape that is well-formed under the empty struct
   context has the same size with or without a context. *)
load "bossLib";
load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val ctx = ``([] : (stcname # struct_info) list)``

val _ = print_eval "ssc_one"
  ``size_of_sh_with_ctxt ^ctx One``
val _ = print_eval "ssc_comb2"
  ``size_of_sh_with_ctxt ^ctx (Comb [One; One])``
val _ = print_eval "ssc_nested"
  ``size_of_sh_with_ctxt ^ctx (Comb [One; Comb [One; One]])``
val _ = print_eval "ssc_wf_one"
  ``is_wf_shape ^ctx One``
val _ = print_eval "ssc_wf_nested"
  ``is_wf_shape ^ctx (Comb [One; Comb [One; One]])``
val _ = print_eval "ssc_eq_one"
  ``(size_of_sh_with_ctxt ^ctx One = size_of_shape One)``
val _ = print_eval "ssc_eq_nested"
  ``(size_of_sh_with_ctxt ^ctx (Comb [One; Comb [One; One]]) =
     size_of_shape (Comb [One; Comb [One; One]]))``
