(* Direct HOL-EVAL fixture for the leaf equations of loop_live$shrink. *)
load "bossLib";
load "preamble";
load "loop_liveTheory";
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

val _ = print_eval "skip"
  ``loop_live$shrink [] (loopLang$Skip : 8 word loopLang$prog)
      (insert 2 () (insert 1 () LN))``;
val _ = print_eval "assign_kept"
  ``loop_live$shrink []
      (loopLang$Assign 1 (loopLang$Const (7w : 8 word)))
      (insert 2 () (insert 1 () LN))``;
val _ = print_eval "dead_assign"
  ``loop_live$shrink []
      (loopLang$Assign 1 (loopLang$Const (7w : 8 word)))
      (insert 2 () LN)``;
val _ = print_eval "live_assign"
  ``loop_live$shrink []
      (loopLang$Assign 1 (loopLang$Var 3 : 8 word loopLang$exp))
      (insert 2 () (insert 1 () LN))``;
val _ = print_eval "arith_div"
  ``loop_live$shrink []
      (loopLang$Arith (loopLang$LDiv 1 2 3))
      (insert 2 () (insert 1 () LN))``;
val _ = print_eval "store"
  ``loop_live$shrink []
      (loopLang$Store (loopLang$Var 4 : 8 word loopLang$exp) 5) LN``;
val _ = print_eval "load32"
  ``loop_live$shrink [] (loopLang$Load32 1 2) LN``;
