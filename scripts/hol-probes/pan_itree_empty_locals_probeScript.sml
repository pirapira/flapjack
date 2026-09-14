(*
  Direct HOL observations for the interaction-tree empty_locals_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:32-34.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val toNum = ``(\(x:8 v). case x of ValWord (w:8 word) => w2n w | _ => 0)``;
val s = ``(s:(8) pan_itreeSem$bstate)``;
val base1 =
  ``(^s with locals := (FEMPTY : (mlstring |-> 8 v)) |+
      (strlit "x", ValWord (5w:8 word)))``;
val base =
  ``((^base1 with globals := (FEMPTY : (mlstring |-> 8 v)) |+
      (strlit "g", ValWord (1w:8 word))) with
      <|memory := (\a. if a = 9w then Word (13w:8 word) else s.memory a);
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

val _ = print_eval "empty_locals_local"
  ``OPTION_MAP ^toNum (FLOOKUP
      (empty_locals ^base).locals (strlit "x"))``;
val _ = print_eval "empty_locals_other"
  ``OPTION_MAP ^toNum (FLOOKUP
      (empty_locals ^base).locals (strlit "other"))``;
val _ = print_eval "empty_locals_global"
  ``OPTION_MAP ^toNum (FLOOKUP
      (empty_locals ^base).globals (strlit "g"))``;
val _ = print_eval "empty_locals_base_addr"
  ``(empty_locals ^base).base_addr = 100w``;
