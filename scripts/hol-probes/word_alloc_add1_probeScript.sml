(* Direct HOL-EVAL oracle for the allocator result on the minimized two-register
   add case.  The source is the post-three_to_two, post-SSA Word program emitted
   by the Pancake pipeline.  Reference: word_allocScript.sml:1791-1820. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
load "riscv_targetTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_allocTheory;
open riscv_targetTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val add1_prog =
  ``wordLang$Seq
      (wordLang$Move 1 [(13,0); (17,2); (21,4)])
      (wordLang$Seq
        (wordLang$Seq
          (wordLang$Move 0 [(25,21)])
          (wordLang$Seq
            (wordLang$Move 0 [(29,17)])
            (wordLang$Inst
              (asm$Arith
                (asm$Binop asm$Add 33 25 (asm$Reg 29))))))
        (wordLang$Seq
          (wordLang$Move 0 [(2,33)])
          (wordLang$Return 13 [2]))) : 64 wordLang$prog``;

val _ = print_eval "add1_allocator"
  ``word_alloc$word_alloc 5 riscv_config 3 22 ^add1_prog NONE``;
