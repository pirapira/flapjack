(*
  Direct CakeML HOL observations for the byte-memory rows of
  ssa_cc_trans_inst (cakeml/compiler/backend/word_allocScript.sml:223-230).
  These are the source-level SSA boundary before word_to_stack lowering.
*)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_allocTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "load8"
  ``full_ssa_cc_trans 0
      (Inst (Mem Load8 1 (Addr 2 (0w:64 word))):64 wordLang$prog)``

val _ = print_eval "store8"
  ``full_ssa_cc_trans 0
      (Inst (Mem Store8 1 (Addr 2 (0w:64 word))):64 wordLang$prog)``
