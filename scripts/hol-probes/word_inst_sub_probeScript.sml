(*
  Direct HOL-EVAL observations for the malformed-`Sub` arities of CakeML's
  `pull_exp` (cakeml/compiler/backend/word_instScript.sml:107-121).

  HOL's `pull_exp_def` matches the dedicated `Op Sub ls` clause before the
  empty/unary fallbacks, so `convert_sub` sees every `Sub` arity.  For a list
  of length 0 or 1 `convert_sub ls = Op Sub ls`, i.e. the node shape survives;
  the empty/unary fallbacks (`op_consts`/`pull_exp x`) must therefore not fire
  for `Sub`.  The Lean counterpart `wordInstPullExp` in
  Flapjack/RiscV/WordInstSelect.lean must reproduce these rows.

  The probe evaluates the original definitions directly; the checked-in .out is
  consumed by Flapjack/Test/WordInstNormalizeParity.lean.
*)
load "bossLib";
load "preamble";
load "word_instTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_instTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "pull_sub_empty"
  ``pull_exp ((Op Sub ([] : 64 wordLang$exp list)) : 64 wordLang$exp)``
val _ = print_eval "pull_sub_unary_var"
  ``pull_exp ((Op Sub [Var (2:num)]) : 64 wordLang$exp)``
val _ = print_eval "pull_sub_unary_const"
  ``pull_exp ((Op Sub [Const (5w:64 word)]) : 64 wordLang$exp)``
val _ = print_eval "norm_sub_empty"
  ``(flatten_exp o pull_exp) ((Op Sub ([] : 64 wordLang$exp list)) : 64 wordLang$exp)``
val _ = print_eval "norm_sub_unary_var"
  ``(flatten_exp o pull_exp) ((Op Sub [Var (2:num)]) : 64 wordLang$exp)``
(* Binary Sub remains unchanged by the clause move: constant second becomes an
   Add with the negated constant first. *)
val _ = print_eval "pull_sub_binary_const"
  ``pull_exp ((Op Sub [Var (7:num); Const (8w:64 word)]) : 64 wordLang$exp)``
val _ = print_eval "norm_sub_binary_const"
  ``(flatten_exp o pull_exp) ((Op Sub [Var (7:num); Const (8w:64 word)]) : 64 wordLang$exp)``
