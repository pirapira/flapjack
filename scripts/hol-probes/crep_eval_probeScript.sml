(*
  Direct HOL observations for crepSem$eval_def.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:90-143.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;
val base =
  ``(^s with <|locals := FEMPTY |+ (1, Word (7w:8 word));
              globals := FEMPTY |+ ((3w:5 word), Word (9w:8 word));
              memaddrs := {10w};
              memory := (\a. if a = 10w then Word (11w:8 word) else Word (0w:8 word));
              base_addr := 100w;
              top_addr := 200w|>)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "eval_const"
  ``crepSem$eval ^base (Const (7w:8 word))``;
val _ = print_eval "eval_local"
  ``crepSem$eval ^base (Var 1)``;
val _ = print_eval "eval_global"
  ``crepSem$eval ^base (LoadGlob (3w:5 word))``;
val _ = print_eval "eval_load"
  ``crepSem$eval ^base (Load (Const (10w:8 word)))``;
val _ = print_eval "eval_op"
  ``crepSem$eval ^base (Op Add [Const (1w:8 word); Const (2w:8 word)])``;
val _ = print_eval "eval_base_addr"
  ``crepSem$eval ^base BaseAddr``;
val _ = print_eval "eval_top_addr"
  ``crepSem$eval ^base TopAddr``;
