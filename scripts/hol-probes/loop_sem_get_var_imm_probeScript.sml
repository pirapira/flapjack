(*
  Direct HOL-EVAL probes for Pancake loopSem$get_var_imm.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:165-167.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(32,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "reg_hit"
  ``loopSem$get_var_imm (Reg 1 : 32 reg_imm)
      (^s with locals := insert 1 (Word 5w) LN)``
val _ = print_eval "reg_miss"
  ``loopSem$get_var_imm (Reg 2 : 32 reg_imm)
      (^s with locals := insert 1 (Word 5w) LN)``
val _ = print_eval "imm_word"
  ``loopSem$get_var_imm (Imm 7w : 32 reg_imm) ^s``
val _ = print_eval "reg_loc"
  ``loopSem$get_var_imm (Reg 1 : 32 reg_imm)
      (^s with locals := insert 1 (wordLang$Loc 9 0) LN)``
