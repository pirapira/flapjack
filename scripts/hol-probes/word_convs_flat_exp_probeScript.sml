(*
  Direct HOL oracle for CakeML backend `wordConvs$flat_exp_conventions`.

  Top-level expressions are forbidden in `Assign`/`Store`; `Set` may only take
  a `Var`; `ShareInst` may only take a `Var` or `Op Add [Var r; Const c]`; and
  the predicate descends through `Seq`, `Loop`, `If`, `MustTerminate` and both
  `Call` bodies.  A `Call` with no return metadata but a handler is still
  checked against the handler body.

  Reference: cakeml/compiler/backend/semantics/wordConvsScript.sml:179-205.
*)
load "bossLib";
load "preamble";
load "wordConvsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordConvsTheory;
open wordLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val good = ``wordLang$Set stackLang$NextFree (wordLang$Var 1) : 8 wordLang$prog``;
val badAssign = ``wordLang$Assign 1 (wordLang$Const (0w:8 word)) : 8 wordLang$prog``;

val () = print_eval "fl_assign" ``flat_exp_conventions ^badAssign``;
val () = print_eval "fl_store" ``flat_exp_conventions
  (wordLang$Store (wordLang$Const (0w:8 word)) 1)``;
val () = print_eval "fl_set_var" ``flat_exp_conventions ^good``;
val () = print_eval "fl_set_op" ``flat_exp_conventions
  (wordLang$Set stackLang$NextFree (wordLang$Op asm$Add
    [wordLang$Var 1; wordLang$Const (0w:8 word)]))``;
val () = print_eval "fl_share_var" ``flat_exp_conventions
  (wordLang$ShareInst asm$Load 1 (wordLang$Var 2))``;
val () = print_eval "fl_share_add" ``flat_exp_conventions
  (wordLang$ShareInst asm$Load 1 (wordLang$Op asm$Add
    [wordLang$Var 2; wordLang$Const (0w:8 word)]))``;
val () = print_eval "fl_share_const" ``flat_exp_conventions
  (wordLang$ShareInst asm$Load 1 (wordLang$Const (0w:8 word)))``;
val () = print_eval "fl_seq_bad" ``flat_exp_conventions
  (wordLang$Seq ^badAssign wordLang$Skip)``;
val () = print_eval "fl_seq_ok" ``flat_exp_conventions
  (wordLang$Seq ^good wordLang$Skip)``;
val () = print_eval "fl_call_none" ``flat_exp_conventions
  (wordLang$Call NONE NONE [] NONE)``;
val () = print_eval "fl_call_handler_bad" ``flat_exp_conventions
  (wordLang$Call NONE NONE [] (SOME (2, ^badAssign, 20, 21)))``;
val () = print_eval "fl_call_ret_bad" ``flat_exp_conventions
  (wordLang$Call (SOME ([1], (sptree$LN, sptree$LN), ^badAssign, 10, 11))
    NONE [] NONE)``;
val () = print_eval "fl_call_both_ok" ``flat_exp_conventions
  (wordLang$Call (SOME ([1], (sptree$LN, sptree$LN), ^good, 10, 11))
    NONE [] (SOME (2, ^good, 20, 21)))``;
val () = print_eval "fl_loop" ``flat_exp_conventions
  (wordLang$Loop sptree$LN ^good sptree$LN)``;
val () = print_eval "fl_if_bad" ``flat_exp_conventions
  (wordLang$If asm$Equal 0 (asm$Reg 1) ^badAssign wordLang$Skip)``;
val () = print_eval "fl_must_terminate" ``flat_exp_conventions
  (wordLang$MustTerminate ^good)``;
val () = print_eval "fl_inst" ``flat_exp_conventions
  (wordLang$Inst (asm$Skip : 8 asm$inst))``;