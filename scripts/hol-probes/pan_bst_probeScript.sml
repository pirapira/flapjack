(*
  Direct HOL observations for bst_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:692-705.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:((8),unit) panSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "locals" ``(bst ^s).locals = s.locals``;
val _ = print_eval "globals" ``(bst ^s).globals = s.globals``;
val _ = print_eval "structs" ``(bst ^s).structs = s.structs``;
val _ = print_eval "code" ``(bst ^s).code = s.code``;
val _ = print_eval "eshapes" ``(bst ^s).eshapes = s.eshapes``;
val _ = print_eval "memory" ``(bst ^s).memory = s.memory``;
val _ = print_eval "memaddrs" ``(bst ^s).memaddrs = s.memaddrs``;
val _ = print_eval "sh_memaddrs" ``(bst ^s).sh_memaddrs = s.sh_memaddrs``;
val _ = print_eval "be" ``(bst ^s).be = s.be``;
val _ = print_eval "base_addr" ``(bst ^s).base_addr = s.base_addr``;
val _ = print_eval "top_addr" ``(bst ^s).top_addr = s.top_addr``;
