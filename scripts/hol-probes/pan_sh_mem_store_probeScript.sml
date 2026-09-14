(*
  Direct HOL observations for panSem$sh_mem_store_def.
  Reference: cakeml/pancake/semantics/panSemScript.sml:528-547.
*)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val s = ``(s:(8,unit) panSem$state)``;
val base = ``(^s with sh_memaddrs := {3w})``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "zero_width_domain_error"
  ``case panSem$sh_mem_store (7w:8 word) (3w:8 word) 0
      (^base with sh_memaddrs := {}) of
      (SOME panSem$Error,s') => s'.clock = s.clock
    | _ => F``;

val _ = print_eval "nonzero_width_domain_error"
  ``case panSem$sh_mem_store (7w:8 word) (3w:8 word) 1
      (^base with sh_memaddrs := {}) of
      (SOME panSem$Error,s') => s'.clock = s.clock
    | _ => F``;
