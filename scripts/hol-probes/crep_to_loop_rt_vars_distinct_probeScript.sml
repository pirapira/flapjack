(* Direct oracle for HOL crep_to_loopProofScript.sml
   all_distinct_ctxt_lookup_all_distinct (:3345):
     ALL_DISTINCT rts /\ distinct_vars ctxt.vars ==>
       ALL_DISTINCT (rt_vars ctxt.vars rts n)
   The rows observe rt_vars on a concrete distinct context: the two-variable
   success case, a singleton, and the OPT_MMAP-failure case [n+1]. *)
load "bossLib";
load "preamble";
load "mlstringTheory";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open finite_mapTheory;
open crep_to_loopProofTheory;

fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

val vars = ``((FEMPTY |+ (1, 10) |+ (2, 20)) : (num, num) fmap)``;

val _ = print_eval "acd_distinct"
  ``ALL_DISTINCT (rt_vars ^vars [1; 2] 0)``;
val _ = print_eval "acd_single"
  ``ALL_DISTINCT (rt_vars ^vars [1] 0)``;
val _ = print_eval "acd_missing"
  ``ALL_DISTINCT (rt_vars ^vars [3] 0)``;
