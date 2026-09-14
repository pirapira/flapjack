(*
  Direct HOL observations for bst_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:692-708.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:('a,'ffi) panSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "bst_locals"
  ``(bst ^s).locals = ^s.locals``;
val _ = print_eval "bst_globals"
  ``(bst ^s).globals = ^s.globals``;
val _ = print_eval "bst_structs"
  ``(bst ^s).structs = ^s.structs``;
val _ = print_eval "bst_code"
  ``(bst ^s).code = ^s.code``;
val _ = print_eval "bst_eshapes"
  ``(bst ^s).eshapes = ^s.eshapes``;
val _ = print_eval "bst_memory"
  ``(bst ^s).memory = ^s.memory``;
val _ = print_eval "bst_memaddrs"
  ``(bst ^s).memaddrs = ^s.memaddrs``;
val _ = print_eval "bst_sh_memaddrs"
  ``(bst ^s).sh_memaddrs = ^s.sh_memaddrs``;
val _ = print_eval "bst_be"
  ``(bst ^s).be = ^s.be``;
val _ = print_eval "bst_base_addr"
  ``(bst ^s).base_addr = ^s.base_addr``;
val _ = print_eval "bst_top_addr"
  ``(bst ^s).top_addr = ^s.top_addr``;

val _ = print_eval "bst_clock_ffi_irrelevant"
  ``(bst (^s with <|clock := 17; ffi := ^s.ffi|>)).locals = ^s.locals``;
