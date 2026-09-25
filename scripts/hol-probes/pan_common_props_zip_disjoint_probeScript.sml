(* Direct HOL-EVAL probes for CakeML Pancake pan_commonProps zip/fupdate and
   disjoint take/drop lemmas (pan_commonPropsScript.sml:289, :399, :413). *)
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

val f = ``((FEMPTY |+ (3, 30)) : (num, num) fmap)``
val upd = ``(^f |++ ZIP ([1;2], [10;20]))``

val _ = print_eval "fzn_notmem"
  ``(FLOOKUP ^upd 9 = FLOOKUP ^f 9)``
val _ = print_eval "fzn_mem"
  ``FLOOKUP ^upd 1``
val _ = print_eval "fzn_preserved"
  ``(FLOOKUP ^upd 3 = FLOOKUP ^f 3)``
val _ = print_eval "dtd_disjoint"
  ``DISJOINT (set (TAKE 2 [1;2;3;4])) (set (TAKE 1 (DROP (2 + 1) [1;2;3;4])))``
val _ = print_eval "ddt_disjoint"
  ``DISJOINT (set (TAKE 1 (DROP (2 + 1) [1;2;3;4]))) (set (TAKE 2 [1;2;3;4]))``
