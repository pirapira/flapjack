(*
  Direct HOL observations for crepSem$sh_mem_load_def.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:168-184.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "sh_mem_load_zero_width_domain_error"
  ``case crepSem$sh_mem_load 1 (3w:8 word) 0
      (^s with sh_memaddrs := {}) of
      (SOME Error,s') => s'.clock = s.clock
    | _ => F``;

val _ = print_eval "sh_mem_load_nonzero_domain_error"
  ``case crepSem$sh_mem_load 1 (3w:8 word) 1
      (^s with sh_memaddrs := {}) of
      (SOME Error,s') => s'.clock = s.clock
    | _ => F``;
