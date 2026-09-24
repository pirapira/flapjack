(* Direct HOL oracle: HOL `make_vmap` is a left fold of `|+`, so when a
   parameter name occurs twice the LAST binding wins (unlike a first-match
   list lookup). *)

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
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

val _ = print_eval "mvd_single_hit"
  (``FLOOKUP (make_vmap [5]) 5 = SOME 0``);
val _ = print_eval "mvd_nodup_second"
  (``FLOOKUP (make_vmap [5;6]) 6 = SOME 1``);
val _ = print_eval "mvd_dup_last_wins"
  (``FLOOKUP (make_vmap [7;7]) 7 = SOME 1``);
