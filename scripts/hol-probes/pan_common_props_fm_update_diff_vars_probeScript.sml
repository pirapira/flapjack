(* Direct HOL-EVAL probes for the CakeML Pancake pan_commonProps
   fm_update_diff_vars lemma (pan_commonPropsScript.sml:780): updating a
   finite map at `a`, then at a distinct key `b`, then at `a` again, then at
   `b` again agrees with updating once at `a` and once at `b`. *)
load "bossLib";
load "preamble";
load "pan_commonPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_commonPropsTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val lhs = ``((FEMPTY |+ (1, 10) |+ (2, 20) |+ (1, 10) |+ (2, 22))
             : (num, num) fmap)``
val rhs = ``((FEMPTY |+ (1, 10) |+ (2, 22)) : (num, num) fmap)``

val _ = print_eval "fmdv_eq_1"
  ``(FLOOKUP ^lhs 1 = FLOOKUP ^rhs 1)``
val _ = print_eval "fmdv_eq_2"
  ``(FLOOKUP ^lhs 2 = FLOOKUP ^rhs 2)``
val _ = print_eval "fmdv_eq_3"
  ``(FLOOKUP ^lhs 3 = FLOOKUP ^rhs 3)``
val _ = print_eval "fmdv_lhs_a" ``FLOOKUP ^lhs 1``
val _ = print_eval "fmdv_lhs_b" ``FLOOKUP ^lhs 2``
val _ = print_eval "fmdv_lhs_absent" ``FLOOKUP ^lhs 3``
