(* Direct HOL oracle for crep_to_loop mk_ctxt_def and make_vmap_def. *)

load "bossLib";
load "preamble";
load "mlstringTheory";
load "crep_to_loopProofTheory";

open bossLib;
open HolKernel Parse;
open preamble;
open mlstringTheory;
open crep_to_loopProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

val vmap = ``((FEMPTY |+ (1, 7) |+ (2, 9)) : (num, num) fmap)``;
val fm = ``((FEMPTY |+ («f», (3, 2))) : (mlstring, num # num) fmap)``;

val _ = print_eval "mk_ctxt_vars"
  (``(mk_ctxt ARMv7 ^vmap ^fm 9).vars = ^vmap``);
val _ = print_eval "mk_ctxt_funcs"
  (``(mk_ctxt ARMv7 ^vmap ^fm 9).funcs = ^fm``);
val _ = print_eval "mk_ctxt_vmax"
  (``(mk_ctxt ARMv7 ^vmap ^fm 9).vmax = 9``);
val _ = print_eval "mk_ctxt_target"
  (``(mk_ctxt ARMv7 ^vmap ^fm 9).target = ARMv7``);
val _ = print_eval "make_vmap_single_hit"
  (``FLOOKUP (make_vmap [5]) 5 = SOME 0``);
val _ = print_eval "make_vmap_two_second"
  (``FLOOKUP (make_vmap [5; 6]) 6 = SOME 1``);
val _ = print_eval "make_vmap_empty_miss"
  (``FLOOKUP (make_vmap []) 5 = NONE``);