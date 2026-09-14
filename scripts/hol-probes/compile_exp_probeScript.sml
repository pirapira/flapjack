(* Direct HOL-EVAL probes for pan_to_crep$compile_exp.
   Reference: cakeml/pancake/pan_to_crepScript.sml:39-101. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;

val ctxt =
  ``<| vars := FEMPTY; funcs := FEMPTY; eids := FEMPTY; vmax := 0 |>``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "leaves"
  ``(pan_to_crep$compile_exp ^ctxt (Const (7w : 8 word)),
    pan_to_crep$compile_exp ^ctxt (Var Global «g»),
    pan_to_crep$compile_exp ^ctxt BaseAddr,
    pan_to_crep$compile_exp ^ctxt TopAddr)``;
val _ = print_eval "struct_field"
  ``(pan_to_crep$compile_exp ^ctxt
      (RStruct [Const (1w : 8 word); Const 2w]),
    pan_to_crep$compile_exp ^ctxt
      (RField 1 (RStruct [Const (1w : 8 word); Const 2w])))``;
val _ = print_eval "loads_ops"
  ``(pan_to_crep$compile_exp ^ctxt (Load32 (Const (3w : 8 word))),
    pan_to_crep$compile_exp ^ctxt (LoadByte (Const (4w : 8 word))),
    pan_to_crep$compile_exp ^ctxt
      (Op Add [Const (1w : 8 word); Const 2w]),
    pan_to_crep$compile_exp ^ctxt
      (Panop Mul [Const (5w : 8 word); Const 6w]))``;
val _ = print_eval "cmp_shift"
  ``(pan_to_crep$compile_exp ^ctxt
      (Cmp Equal (Const (1w : 8 word)) (Const 0w)),
    pan_to_crep$compile_exp ^ctxt
      (Shift Lsl (Const (2w : 8 word)) (Const 1w)))``;
