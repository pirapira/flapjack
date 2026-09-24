(*
  Direct HOL observations for local riscv_targetProof$length_riscv_encode.
  The theorem quantifies over HOL's full riscv$instruction datatype.
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
    print (term_to_string (rconc th));
    print "\n"
  end

val _ = print_eval "riscv_encode_length_addi"
  ``LENGTH (riscv_encode (ArithI (ADDI (0w, 0w, 0w)))) = 4``;
val _ = print_eval "riscv_encode_length_add"
  ``LENGTH (riscv_encode (ArithR (ADD (1w, 2w, 3w)))) = 4``;
val _ = print_eval "riscv_encode_length_branch"
  ``LENGTH (riscv_encode (Branch (BEQ (1w, 2w, 4w)))) = 4``;
val _ = print_eval "riscv_encode_length_load"
  ``LENGTH (riscv_encode (Load (LD (1w, 2w, 0w)))) = 4``;
