(* Direct inspection of the proved Cake semanticsProps implements'_trans theorem.
   Reference: cakeml/semantics/proofs/semanticsPropsScript.sml:285-295. *)
load "bossLib";
load "semanticsPropsTheory";
open bossLib HolKernel Parse semanticsPropsTheory;

val _ = print "implements_prime_trans=";
val _ = print_term (concl implements'_trans);
val _ = print "\n";
