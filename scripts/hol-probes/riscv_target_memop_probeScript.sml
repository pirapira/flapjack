(*
  Direct CakeML HOL observations for riscv_memop, the target opcode
  selection boundary in compiler/encoders/riscv/riscv_targetScript.sml:68-74.
*)
load "bossLib";
load "preamble";
load "riscv_targetTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open riscv_targetTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "load32" ``riscv_memop Load32``
val _ = print_eval "load16" ``riscv_memop Load16``
val _ = print_eval "load8" ``riscv_memop Load8``
val _ = print_eval "load" ``riscv_memop Load``
val _ = print_eval "store32" ``riscv_memop Store32``
val _ = print_eval "store16" ``riscv_memop Store16``
val _ = print_eval "store8" ``riscv_memop Store8``
val _ = print_eval "store" ``riscv_memop Store``
