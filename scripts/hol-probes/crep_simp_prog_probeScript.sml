(* Direct HOL-EVAL fixture for crep_arith$simp_prog_def. *)
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

val _ = print_eval "assign"
  ``crep_arith$simp_prog
      (Assign 1 (Crepop Mul [Var 2; Const (2w : 8 word)]))``;
val _ = print_eval "dec_return"
  ``crep_arith$simp_prog
      (Dec 1 (Crepop Mul [Const (2w : 8 word); Const (3w : 8 word)])
        (Return [Var 1]))``;
val _ = print_eval "store"
  ``crep_arith$simp_prog
      (Store (Var 2) (Crepop Mul [Var 3; Const (2w : 8 word)]))``;
val _ = print_eval "store32"
  ``crep_arith$simp_prog
      (Store32 (Var 2) (Crepop Mul [Var 3; Const (2w : 8 word)]))``;
val _ = print_eval "store_byte"
  ``crep_arith$simp_prog
      (StoreByte (Var 2) (Crepop Mul [Var 3; Const (2w : 8 word)]))``;
val _ = print_eval "store_glob"
  ``crep_arith$simp_prog
      (StoreGlob (4w : 5 word)
        (Crepop Mul [Var 3; Const (2w : 8 word)]))``;
val _ = print_eval "seq_if_while"
  ``crep_arith$simp_prog
      (Seq
        (If (Crepop Mul [Var 2; Const (2w : 8 word)])
          (Assign 1 (Const (4w : 8 word)))
          (While (Crepop Mul [Var 3; Const (2w : 8 word)]) Skip))
        (Return [Crepop Mul [Var 4; Const (2w : 8 word)]]))``;
val _ = print_eval "call_tail"
  ``crep_arith$simp_prog
      (Call NONE «f» [Crepop Mul [Var 2; Const (2w : 8 word)]])``;
val _ = print_eval "call_handler"
  ``crep_arith$simp_prog
      (Call (SOME ([1], SOME ((7w : 8 word),
        Assign 2 (Crepop Mul [Var 3; Const (2w : 8 word)]))))
        «f» [Var 4])``;
val _ = print_eval "return_shmem"
  ``crep_arith$simp_prog
      (Seq
        (ShMem Load 1 (Crepop Mul [Var 2; Const (2w : 8 word)]))
        (Return [Crepop Mul [Var 3; Const (2w : 8 word)]]))``;
val _ = print_eval "unchanged"
  ``crep_arith$simp_prog (Break 3)``;
