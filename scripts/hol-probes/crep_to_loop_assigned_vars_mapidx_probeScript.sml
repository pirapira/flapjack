load "bossLib";
load "preamble";
load "loopLangTheory";
load "rich_listTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopLangTheory;
open rich_listTheory;

fun print_eval label q = let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* assigned_vars_MAPi_Assign (cakeml/pancake/proofs/crep_to_loopProofScript.sml:355):
   assigned_vars (nested_seq (MAPi (\n. Assign (n + offset)) les)) =
     GENLIST ($+ offset) (LENGTH les).  Observed for empty, one, two and three
   element expression lists and several offsets. *)
val _ = print_eval "avma_nil"
  ``loopLang$assigned_vars (loopLang$nested_seq (MAPi (\n. loopLang$Assign (n + 3)) ([] : 64 word exp list))) =
    GENLIST (\n. n + 3) (LENGTH ([] : 64 word exp list))``;
val _ = print_eval "avma_one"
  ``loopLang$assigned_vars (loopLang$nested_seq (MAPi (\n. loopLang$Assign (n + 5)) ([Var 0] : 64 word exp list))) =
    GENLIST (\n. n + 5) (LENGTH ([Var 0] : 64 word exp list))``;
val _ = print_eval "avma_two"
  ``loopLang$assigned_vars (loopLang$nested_seq (MAPi (\n. loopLang$Assign (n + 3)) ([Var 0; Var 1] : 64 word exp list))) =
    GENLIST (\n. n + 3) (LENGTH ([Var 0; Var 1] : 64 word exp list))``;
val _ = print_eval "avma_three"
  ``loopLang$assigned_vars (loopLang$nested_seq (MAPi (\n. loopLang$Assign (n + 7)) ([Var 0; Var 1; Var 2] : 64 word exp list))) =
    GENLIST (\n. n + 7) (LENGTH ([Var 0; Var 1; Var 2] : 64 word exp list))``;
val _ = print_eval "avma_offset_zero"
  ``loopLang$assigned_vars (loopLang$nested_seq (MAPi (\n. loopLang$Assign (n + 0)) ([Var 0; Var 1] : 64 word exp list))) =
    GENLIST (\n. n + 0) (LENGTH ([Var 0; Var 1] : 64 word exp list))``;
