(* Direct HOL oracle rows for panLang$size_of_shape
   (cakeml/pancake/panLangScript.sml:174-177). *)
load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val one = ``(panLang$One : panLang$shape)``;
val comb = ``panLang$Comb [panLang$One; panLang$Comb [panLang$One; panLang$One]]``;
val named = ``panLang$Named «A»``;

val _ = print_eval "ss_one" ``size_of_shape ^one``;
val _ = print_eval "ss_comb" ``size_of_shape ^comb``;
val _ = print_eval "ss_named" ``size_of_shape ^named``;
val _ = print_eval "ss_eq" ``size_of_shape ^comb = 3n``;