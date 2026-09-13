(*
  Probe the original CakeML word-level LongDiv helper code.

  Reference: cakeml/compiler/backend/data_to_wordScript.sml:829-867.
  RISC-V has_longdiv=false selects LongDiv1_code rather than encoding the
  LongDiv instruction itself.  This fixture is intentionally source-derived;
  it is not a second implementation in Lean.
*)
load "bossLib";
load "preamble";
load "data_to_wordTheory";
load "riscv_targetTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open data_to_wordTheory;
open riscv_targetTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val software_conf =
  ``(data_conf with has_longdiv := F)``;

val _ = print_eval "longdiv_code_software"
  ``LongDiv_code ^software_conf``;
val _ = print_eval "longdiv1_code_software"
  ``LongDiv1_code ^software_conf``;
val _ = print_eval "riscv_longdiv_encoding"
  ``riscv_ast (Inst (Arith (LongDiv 0 3 3 0 6)))``;
