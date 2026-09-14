(* Direct HOL-EVAL observations for word_alloc$get_forced on RISC-V.
   Reference: cakeml/compiler/backend/word_allocScript.sml:1466-1513. *)
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

val _ = print_eval "add_carry"
  ``get_forced riscv_config
      (Inst (Arith (AddCarry 1 2 3 4))) []``;
val _ = print_eval "long_mul"
  ``get_forced riscv_config
      (Inst (Arith (LongMul 1 2 3 4))) []``;
val _ = print_eval "nested"
  ``get_forced riscv_config
      (Seq (Inst (Arith (AddCarry 1 2 3 4)))
        (MustTerminate (Inst (Arith (LongMul 1 2 3 4))))) []``;
