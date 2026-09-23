(* Direct HOL-EVAL fixture for the canonical FCP index and n2w bit order.
   The source definition is HOL4's wordsTheory.n2w_def in
   $HOL/src/n-bit/wordsScript.sml. *)
load "bossLib";
load "bitTheory";
load "boolLib";
load "Rewrite";
load "Conv";
load "Drule";
load "wordsTheory";
open bossLib;
open bitTheory;
open boolLib;
open Rewrite;
open Conv;
open Drule;
open HolKernel Parse;
open wordsTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (concl th);
    print "\n"
  end

fun print_thm label th =
  (
    print (label ^ "=");
    print_term (concl th);
    print "\n"
  )

fun print_bit label q =
  let
    val th = SIMP_CONV (srw_ss())
      [BIT_def, BITS_THM, MOD_2EXP_def, DIV_2EXP_def, BIT0_ODD] q
  in
    print (label ^ "=");
    print_term (concl th);
    print "\n"
  end

val _ = print_eval "n2w_zero_word" ``(n2w 0 : 8 word)``;
val _ = print_eval "n2w_one_word" ``(n2w 1 : 8 word)``;
val _ = print_eval "n2w_high_word" ``(n2w 128 : 8 word)``;
val _ = print_thm "dimindex8" dimindex_8;
val _ = print_thm "n2w_zero_bit0"
  (INST_TYPE [alpha |-> ``:8``]
    (SPECL [``0:num``, ``0:num``] word_index_n2w));
val _ = print_thm "n2w_one_bit0"
  (INST_TYPE [alpha |-> ``:8``]
    (SPECL [``1:num``, ``0:num``] word_index_n2w));
val _ = print_thm "n2w_one_bit1"
  (INST_TYPE [alpha |-> ``:8``]
    (SPECL [``1:num``, ``1:num``] word_index_n2w));
val _ = print_thm "n2w_high_bit7"
  (INST_TYPE [alpha |-> ``:8``]
    (SPECL [``128:num``, ``7:num``] word_index_n2w));
val _ = print_thm "n2w_high_bit6"
  (INST_TYPE [alpha |-> ``:8``]
    (SPECL [``128:num``, ``6:num``] word_index_n2w));
val _ = print_bit "bit_zero0" ``BIT 0 0``;
val _ = print_bit "bit_one0" ``BIT 0 1``;
val _ = print_bit "bit_one1" ``BIT 1 1``;
val _ = print_bit "bit_high7" ``BIT 7 128``;
val _ = print_bit "bit_high6" ``BIT 6 128``;
