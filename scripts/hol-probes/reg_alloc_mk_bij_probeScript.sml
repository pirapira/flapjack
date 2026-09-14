(* Direct HOL-EVAL observations for CakeML's reg_alloc mk_bij/list_remap.
   Reference: cakeml/compiler/backend/reg_alloc/reg_allocScript.sml:1096-1122. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open reg_allocTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

fun print_bij label tree =
  let
    val result = ``mk_bij ^tree``
  in
    print_eval (label ^ "_to") ``sptree$toAList (FST (^result))``;
    print_eval (label ^ "_from") ``sptree$toAList (FST (SND (^result)))``;
    print_eval (label ^ "_next") ``SND (SND (^result))``
  end

val _ = print_bij "empty" ``Seq (Delta [] []) (Set LN)``;
val _ = print_bij "delta" ``Delta [1;2] [2;3]``;
val _ = print_bij "set" ``Set (fromList [();();()])``;
val _ = print_bij "seq" ``Seq (Delta [1] [2]) (Set (fromList [();();()]))``;
