(* Direct HOL-EVAL fixture for crep_arith$dest_const. *)
load "bossLib";
load "preamble";
load "crep_arithTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "constant"
  ``crep_arith$dest_const (crepLang$Const (7w : 8 word))``;
val _ = print_eval "variable"
  ``crep_arith$dest_const (crepLang$Var 2 : 8 word crepLang$exp)``;
val _ = print_eval "load"
  ``crep_arith$dest_const
      (crepLang$Load (crepLang$Const (3w : 8 word)))``;
val _ = print_eval "multiplication"
  ``crep_arith$dest_const
      (crepLang$Crepop crepLang$Mul
        [crepLang$Const (2w : 8 word); crepLang$Const (4w : 8 word)])``;
(* Word-carrier convention rows: HOL `'a word` is literally `bool[dimindex(:'a)]`
   (a finite boolean function space) and `dimindex` is always positive, which is
   the property encoded by `[NeZero width]` on the width-indexed Lean tags. *)
val _ = print_eval "word_carrier_bool"
  (``((7w : 8 word) : bool[8]) = 7w``);
val _ = print_eval "dimindex_8"
  (``dimindex (:8) = 8``);
val _ = print_eval "dimindex_pos"
  (``0 < dimindex (:8)``);
