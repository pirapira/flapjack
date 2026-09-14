(*
  Direct HOL observations for crepSem$sh_mem_op_def.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:210-219.
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

val _ = print_eval "sh_mem_op_load_domain_error"
  ``case crepSem$sh_mem_op Load 1 (3w:8 word)
      (^s with sh_memaddrs := {}) of
      (SOME Error,s') => s'.clock = s.clock
    | _ => F``;

val _ = print_eval "sh_mem_op_store_domain_error"
  ``case crepSem$sh_mem_op Store 1 (3w:8 word)
      (^s with <|locals := FEMPTY |+ (1, Word (7w:8 word));
                   sh_memaddrs := {}|>) of
      (SOME Error,s') => s'.clock = s.clock
    | _ => F``;
