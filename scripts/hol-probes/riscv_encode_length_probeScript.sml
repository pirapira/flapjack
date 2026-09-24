(*
  Direct HOL observations for local riscv_targetProof$length_riscv_encode.
  The theorem quantifies over HOL's full riscv$instruction datatype.
*)

load "bossLib";
load "preamble";
load "bitstringLib";
load "riscvTheory";
load "riscv_targetTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open riscvTheory;
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

(* Use the encoder's production compute setup so the oracle exposes bytes,
   rather than stopping at symbolic slices of Encode. *)
fun riscv_type s = Type.mk_thy_type {Thy = "riscv", Tyop = s, Args = []};
val riscv_tys =
  List.map riscv_type
    ["instruction", "Shift", "ArithI", "ArithR", "MulDiv", "Branch",
     "Load", "Store"];
val riscv_bytes_conv =
  computeLib.compset_conv (wordsLib.words_compset)
    [computeLib.Defs
      [riscv_ast_def, riscv_encode_def, riscv_const32_def,
       riscv_bop_r_def, riscv_bop_i_def, riscv_sh_def, riscv_memop_def,
       Encode_def, opc_def, Itype_def, Rtype_def, Stype_def, SBtype_def,
       Utype_def, UJtype_def],
     computeLib.Convs
       [(bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)],
     computeLib.Tys
       ([sumSyntax.mk_sum(alpha,beta),
         mk_thy_type{Thy="asm",Tyop="cmp",Args=[]}] @ riscv_tys),
     computeLib.Extenders [pairLib.add_pair_compset]];
val _ =
  let
    val th = riscv_bytes_conv
      ``riscv_encode (ArithI (ADDI (5w, 3w, 2047w)))``
  in
    print "riscv_encode_bytes_addi=";
    print (term_to_string (rconc th));
    print "\n"
  end;

val _ =
  let
    val th = riscv_bytes_conv
      ``riscv_encode (ArithR (ADD (5w, 3w, 7w)))``
  in
    print "riscv_encode_bytes_add=";
    print (term_to_string (rconc th));
    print "\n"
  end;
