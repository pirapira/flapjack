(*
  Direct HOL-EVAL fixture for Pancake loopSem eval_def.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:71-93.
  The output is consumed by Flapjack.Test.LoopEvalParity; only source-derived
  values are recorded here.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(8,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "const"
  ``eval ^s (Const (7w : 8 word))``
val _ = print_eval "var_hit"
  ``eval (^s with locals := insert 2 (Word (7w : 8 word)) LN) (Var 2)``
val _ = print_eval "var_miss"
  ``eval (^s with locals := LN) (Var 2)``
val _ = print_eval "lookup_hit"
  ``eval (^s with globals := FEMPTY |+ (3w, Word (9w : 8 word))) (Lookup 3w)``
val _ = print_eval "lookup_miss"
  ``eval (^s with globals := FEMPTY) (Lookup 3w)``
val _ = print_eval "load_hit"
  ``eval (^s with <| mdomain := {3w};
                    memory := (3w =+ Word (11w : 8 word)) (^s).memory |>)
      (Load (Const (3w : 8 word)))``
val _ = print_eval "load_miss"
  ``eval (^s with <| mdomain := {3w};
                    memory := (3w =+ Word (11w : 8 word)) (^s).memory |>)
      (Load (Const (4w : 8 word)))``
val _ = print_eval "op_add_three"
  ``eval ^s (Op Add [Const (1w : 8 word); Const 2w; Const 3w])``
val _ = print_eval "op_and_empty"
  ``eval ^s (Op And [])``
val _ = print_eval "op_sub_bad_arity"
  ``eval ^s (Op Sub [Const (7w : 8 word)])``
val _ = print_eval "shift_ror"
  ``eval ^s (Shift Ror (Const (129w : 8 word)) (Const (1w : 8 word)))``
val _ = print_eval "shift_out_of_range"
  ``eval ^s (Shift Lsl (Const (1w : 8 word)) (Const (8w : 8 word)))``
val _ = print_eval "base_addr"
  ``eval (^s with base_addr := (4w : 8 word)) BaseAddr``
val _ = print_eval "top_addr"
  ``eval (^s with top_addr := (100w : 8 word)) TopAddr``
