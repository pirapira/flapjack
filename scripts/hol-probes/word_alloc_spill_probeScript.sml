(* Direct HOL-EVAL oracle for the same post-SSA add program as the
   word_alloc_add1 probe, using Cake's algorithm 1 (simple allocator with
   spill heuristics) and its 22-register RISC-V allocation boundary. *)
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

val spill_prog =
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

val _ = print_eval "spill_allocator"
  ``word_alloc$word_alloc 5 riscv_config 1 22 ^spill_prog NONE``;

val _ = print_eval "spill_allocator_simple_unweighted"
  ``word_alloc$word_alloc 5 riscv_config 0 22 ^spill_prog NONE``;

val _ = print_eval "spill_allocator_linear_scan"
  ``word_alloc$word_alloc 5 riscv_config 4 22 ^spill_prog NONE``;

val _ = print_eval "spill_allocator_linear_scan_k1"
  ``word_alloc$word_alloc 5 riscv_config 4 1 ^spill_prog NONE``;

val _ = print_eval "spill_allocator_k1"
  ``word_alloc$word_alloc 5 riscv_config 3 1 ^spill_prog NONE``;

val _ = print_eval "spill_allocator_k1_unweighted"
  ``word_alloc$word_alloc 5 riscv_config 2 1 ^spill_prog NONE``;

val add_carry_prog =
  ``wordLang$Seq
      (wordLang$Move 1 [(13,0); (17,2); (21,4); (25,6)])
      (wordLang$Seq
        (wordLang$Inst
          (asm$Arith (asm$AddCarry 29 25 21 17)))
        (wordLang$Return 13 [29;17])) : 64 wordLang$prog``;

val _ = print_eval "add_carry_allocator"
  ``word_alloc$word_alloc 5 riscv_config 3 22 ^add_carry_prog NONE``;
