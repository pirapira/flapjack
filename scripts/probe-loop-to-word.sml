(* Original-definition probe for Flapjack/Test/LoopToWordFixture.lean.

   Evaluates the CakeML Pancake loop-to-word register-context functions with
   HOL4 EVAL and prints the results consumed by the Lean fixture:

     find_var      cakeml/pancake/loop_to_wordScript.sml:10
     find_reg_imm  cakeml/pancake/loop_to_wordScript.sml:17
     make_ctxt     cakeml/pancake/loop_to_wordScript.sml:152

   Regeneration (HOL4 + CakeML sources on the load path):

     cd <cakeml>/pancake
     Holmake loop_to_wordTheory
     <hol> < scripts/probe-loop-to-word.sml

   The printed values are the original results.  Transcribe them into
   Flapjack/Test/LoopToWordFixture.lean under the matching case labels. *)

open HolKernel boolLib bossLib;
open sptreeTheory;
open loop_to_wordTheory;

fun emit (label, tm) =
  print (label ^ " = " ^ term_to_string (rhs (concl (EVAL tm))) ^ "\n");

val probes = [
  ("find_var.empty.0",     ``find_var (LN : num |-> num) 0``),
  ("find_var.empty.99",    ``find_var (LN : num |-> num) 99``),
  ("find_var.single.hit",  ``find_var (insert 3 7 (LN : num |-> num)) 3``),
  ("find_var.single.miss", ``find_var (insert 3 7 (LN : num |-> num)) 4``),
  ("find_var.ctxt.10",     ``find_var (make_ctxt 2 [10;11;12] LN) 10``),
  ("find_var.ctxt.11",     ``find_var (make_ctxt 2 [10;11;12] LN) 11``),
  ("find_var.ctxt.12",     ``find_var (make_ctxt 2 [10;11;12] LN) 12``),
  ("find_var.ctxt.99",     ``find_var (make_ctxt 2 [10;11;12] LN) 99``),
  ("find_var.ctxt4.1",     ``find_var (make_ctxt 4 [1;2] LN) 1``),
  ("find_var.ctxt4.2",     ``find_var (make_ctxt 4 [1;2] LN) 2``),
  ("find_var.ctxt4.9",     ``find_var (make_ctxt 4 [1;2] LN) 9``),
  ("find_reg_imm.imm",     ``find_reg_imm (LN : num |-> num) (Imm 5 : 'a reg_imm)``),
  ("find_reg_imm.reg.miss",``find_reg_imm (LN : num |-> num) (Reg 11 : 'a reg_imm)``),
  ("find_reg_imm.reg.hit", ``find_reg_imm (insert 11 4 (LN : num |-> num)) (Reg 11 : 'a reg_imm)``)
];

val _ = app emit probes;
