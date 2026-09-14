(* Direct HOL-EVAL probe for pan_to_crep$compile_panop.
   Reference: cakeml/pancake/pan_to_crepScript.sml:35. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;

val theorem = EVAL ``pan_to_crep$compile_panop panLang$Mul``;
print_term (rconc theorem);
print "\n";
