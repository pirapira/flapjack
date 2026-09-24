load "bossLib";
load "preamble";
load "pan_commonPropsTheory";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_commonPropsTheory panLangTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

val fm = ``((FEMPTY |+ («x», (panLang$One, [1;2])) |+ («y», (panLang$One, [3;4]))) :
            (mlstring, panLang$shape # num list) fmap)``;

(* `no_overlap` is a predicate, so project its defining lookup facts. *)
val _ = print_eval "slot_nodup_x"
  ``case FLOOKUP ^fm «x» of SOME (sh,xs) => ALL_DISTINCT xs | NONE => F``;
val _ = print_eval "slot_nodup_y"
  ``case FLOOKUP ^fm «y» of SOME (sh,xs) => ALL_DISTINCT xs | NONE => F``;
(* disjointness of the two distinct variables' slot lists *)
val _ = print_eval "slots_disjoint"
  ``~(MEM (1:num) [3;4]) /\ ~(MEM (2:num) [3;4])``;
val _ = print_eval "distinct_lists_self"
  ``pan_common$distinct_lists [1;2] [3;4] = pan_common$distinct_lists [1;2] [3;4]``;
