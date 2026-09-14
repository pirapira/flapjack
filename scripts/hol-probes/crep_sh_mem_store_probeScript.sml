(*
  Direct HOL observations for crepSem$sh_mem_store_def.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:186-208.
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

val _ = print_eval "sh_mem_store_missing_local"
  ``case crepSem$sh_mem_store 1 (3w:8 word) 0
      (^s with <|locals := FEMPTY; sh_memaddrs := {}|>) of
      (SOME Error,s') => s'.clock = s.clock
    | _ => F``;

val _ = print_eval "sh_mem_store_zero_width_domain_error"
  ``case crepSem$sh_mem_store 1 (3w:8 word) 0
      (^s with <|locals := FEMPTY |+ (1, Word (7w:8 word));
                   sh_memaddrs := {}|>) of
      (SOME Error,s') => s'.clock = s.clock
    | _ => F``;

val _ = print_eval "sh_mem_store_nonzero_domain_error"
  ``case crepSem$sh_mem_store 1 (3w:8 word) 1
      (^s with <|locals := FEMPTY |+ (1, Word (7w:8 word));
                   sh_memaddrs := {}|>) of
      (SOME Error,s') => s'.clock = s.clock
    | _ => F``;
