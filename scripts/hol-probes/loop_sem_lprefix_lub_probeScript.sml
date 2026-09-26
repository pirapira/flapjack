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
    val source = SIMP_CONV (srw_ss())
      [lprefix_lubTheory.build_lprefix_lub_def,
       lprefix_lubTheory.build_lprefix_lub_f_def,
       lprefix_lubTheory.lprefix_chain_nth_def,
       llistTheory.LNTH_fromList,
       optionTheory.some_def, Once LUNFOLD] q
    val th = EVAL (rconc source)
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val empty_chain = ``({} : num llist -> bool)``;
val singleton_family = ``(\ll. ll = llist$fromList [1])``;
val prefix_chain =
  ``(\ll. ll = llist$fromList [1] \/ ll = llist$fromList [1;2])``;
val conflicting_prefixes =
  ``(\ll. ll = llist$fromList [1] \/ ll = llist$fromList [2])``;
val conflicting_suffixes =
  ``(\ll. ll = llist$fromList [1;2] \/ ll = llist$fromList [1;3])``;

val _ = print_eval "empty_lub_0" ``LNTH 0 (lprefix_lub$build_lprefix_lub ^empty_chain)``;
val _ = print_eval "singleton_lub_0"
  ``LNTH 0 (lprefix_lub$build_lprefix_lub ^singleton_family)``;
val _ = print_eval "singleton_lub_1"
  ``LNTH 1 (lprefix_lub$build_lprefix_lub ^singleton_family)``;
val _ = print_eval "prefix_chain_lub_0"
  ``LNTH 0 (lprefix_lub$build_lprefix_lub ^prefix_chain)``;
val _ = print_eval "prefix_chain_lub_1"
  ``LNTH 1 (lprefix_lub$build_lprefix_lub ^prefix_chain)``;
(* Outside lprefix_chain, HOL's selected element is not characterized by
   build_lprefix_lub_thm; record the concrete choice made by this HOL run. *)
val _ = print_eval "conflicting_prefixes_lub_0"
  ``LNTH 0 (lprefix_lub$build_lprefix_lub ^conflicting_prefixes)``;
val _ = print_eval "conflicting_prefixes_lub_1"
  ``LNTH 1 (lprefix_lub$build_lprefix_lub ^conflicting_prefixes)``;
val _ = print_eval "conflicting_suffixes_lub_0"
  ``LNTH 0 (lprefix_lub$build_lprefix_lub ^conflicting_suffixes)``;
val _ = print_eval "conflicting_suffixes_lub_1"
  ``LNTH 1 (lprefix_lub$build_lprefix_lub ^conflicting_suffixes)``;
