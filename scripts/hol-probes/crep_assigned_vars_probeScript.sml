(* Direct HOL-EVAL observations for the Crepe assigned-variable properties that
   the Lean ports in Flapjack/Pancake/Semantics/CrepProps.lean must match.

   Reference:
     cakeml/pancake/semantics/crepPropsScript.sml:
       assigned_free_vars_IMP_assigned_vars (:373)
       nested_seq_assigned_vars_eq           (:411)
       nested_seq_assigned_free_vars_eq      (:420)

   The rows pin, on concrete programs, that every free variable is an assigned
   variable, and that `nested_seq (MAP2 Assign ns vs)` assigns exactly `ns`.
*)
load "bossLib";
load "preamble";
load "crepPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepPropsTheory;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val prog =
  ``(crepLang$Dec 1 (crepLang$Const (1w : 8 word))
       (crepLang$Seq (crepLang$Assign 2 (crepLang$Var 1))
         (crepLang$Assign 3 (crepLang$Const (2w : 8 word)))))
     : 8 crepLang$prog``;

val nested =
  ``(crepLang$nested_seq
     (MAP2 crepLang$Assign [1; 2]
       [crepLang$Const (1w : 8 word); crepLang$Const (2w : 8 word)]))
     : 8 crepLang$prog``;

val _ = print_eval "afv_prog" ``assigned_free_vars ^prog``;
val _ = print_eval "av_prog" ``assigned_vars ^prog``;
val _ = print_eval "imp_mem"
  ``MEM 2 (assigned_free_vars ^prog) ==> MEM 2 (assigned_vars ^prog)``;
val _ = print_eval "imp_mem_absent"
  ``MEM 9 (assigned_free_vars ^prog) ==> MEM 9 (assigned_vars ^prog)``;
val _ = print_eval "nested_av" ``assigned_vars ^nested``;
val _ = print_eval "nested_afv" ``assigned_free_vars ^nested``;