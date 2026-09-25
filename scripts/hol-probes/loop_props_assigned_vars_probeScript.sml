load "bossLib";
load "preamble";
load "loopPropsTheory";
load "rich_listTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopPropsTheory;
open loopLangTheory;
open rich_listTheory;

fun print_eval label q = let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* assigned_vars_seq_split (cakeml/pancake/semantics/loopPropsScript.sml:890):
   assigned_vars (Seq p q) = assigned_vars p ++ assigned_vars q. *)
val _ = print_eval "avs_seq_split"
  ``loopLang$assigned_vars (loopLang$Seq (loopLang$Assign 1 (Var 0)) (loopLang$Assign 2 (Var 1))) =
    loopLang$assigned_vars (loopLang$Assign 1 (Var 0)) ++ loopLang$assigned_vars (loopLang$Assign 2 (Var 1))``;

(* assigned_vars_nested_seq_split (:880):
   assigned_vars (nested_seq (p ++ q)) =
     assigned_vars (nested_seq p) ++ assigned_vars (nested_seq q). *)
val _ = print_eval "avs_nested_seq_split_two"
  ``loopLang$assigned_vars (loopLang$nested_seq ([loopLang$Assign 1 (Var 0); loopLang$Assign 2 (Var 1)] ++ [loopLang$Assign 3 (Var 2)])) =
    loopLang$assigned_vars (loopLang$nested_seq [loopLang$Assign 1 (Var 0); loopLang$Assign 2 (Var 1)]) ++
    loopLang$assigned_vars (loopLang$nested_seq [loopLang$Assign 3 (Var 2)])``;
val _ = print_eval "avs_nested_seq_split_nil"
  ``loopLang$assigned_vars (loopLang$nested_seq (([] : 64 word prog list) ++ [loopLang$Assign 4 (Var 0)])) =
    loopLang$assigned_vars (loopLang$nested_seq ([] : 64 word prog list)) ++
    loopLang$assigned_vars (loopLang$nested_seq [loopLang$Assign 4 (Var 0)])``;

(* assigned_vars_nested_assign (:897):
   LENGTH xs = LENGTH ys ==> assigned_vars (nested_seq (MAP2 Assign xs ys)) = xs. *)
val _ = print_eval "avs_nested_assign_nil"
  ``loopLang$assigned_vars (loopLang$nested_seq (MAP2 loopLang$Assign ([] : num list) ([] : 64 word exp list))) =
    ([] : num list)``;
val _ = print_eval "avs_nested_assign_one"
  ``loopLang$assigned_vars (loopLang$nested_seq (MAP2 loopLang$Assign [7] ([Var 0] : 64 word exp list))) =
    [7]``;
val _ = print_eval "avs_nested_assign_three"
  ``loopLang$assigned_vars (loopLang$nested_seq (MAP2 loopLang$Assign [3; 4; 5] ([Var 0; Var 1; Var 2] : 64 word exp list))) =
    [3; 4; 5]``;
