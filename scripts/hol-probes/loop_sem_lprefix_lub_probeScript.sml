(*)
  Direct HOL observations for the canonical build_lprefix_lub boundary used
  by loopSem$semantics.  Reference: lprefix_lubScript.sml:430-455 and
  loopSemScript.sml:529-533.
*)
load "bossLib";
load "preamble";
load "loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open lprefix_lubTheory;

fun print_eval label q =
  let
    val th = SIMP_CONV (srw_ss())
      [lprefix_lubTheory.build_lprefix_lub_def,
       lprefix_lubTheory.build_lprefix_lub_f_def,
       lprefix_lubTheory.lprefix_chain_nth_def,
       optionTheory.some_def, Once LUNFOLD] q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val empty_chain = ``({} : num llist -> bool)``;

val _ = print_eval "empty_lub_0" ``LNTH 0 (lprefix_lub$build_lprefix_lub ^empty_chain)``;
