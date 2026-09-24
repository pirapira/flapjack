(*
  Direct HOL observations for the crepSem StoreByte evaluator case at a
  NONZERO byte offset.  Reference: cakeml/pancake/semantics/crepSemScript.sml
  (`eval_def`/StoreByte case) and cakeml/pancake/semantics/panSemScript.sml
  (`mem_store_byte_def`, `set_byte` from HOL/src/n-bit/byteScript.sml).  The
  memory cell holds 0x1122334455667788 at address 8 and `memaddrs = {8w}`.
  Little-endian byte order: storing 0xAA at address 8 yields
  0x11223344556677AA, and at address 9 yields 0x112233445566AA88.  An address
  outside `memaddrs` yields `SOME Error` with the memory unchanged.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(64,unit) crepSem$state)``;
val s0 = ``(^s with <|
    memory := (\(a : 64 word).
      if a = (8w:64 word) then Word (0x1122334455667788w:64 word)
      else Word (0w:64 word));
    memaddrs := {(8w:64 word)};
    be := F |>)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "storebyte_offset9_result"
  ``FST (crepSem$evaluate
      (crepLang$StoreByte (crepLang$Const (9w:64 word))
        (crepLang$Const (0xAAw:64 word)), ^s0))``;

val _ = print_eval "storebyte_offset9_mem8"
  ``(SND (crepSem$evaluate
      (crepLang$StoreByte (crepLang$Const (9w:64 word))
        (crepLang$Const (0xAAw:64 word)), ^s0))).memory (8w:64 word)``;

val _ = print_eval "storebyte_offset8_mem8"
  ``(SND (crepSem$evaluate
      (crepLang$StoreByte (crepLang$Const (8w:64 word))
        (crepLang$Const (0xAAw:64 word)), ^s0))).memory (8w:64 word)``;

val _ = print_eval "storebyte_outside_domain_result"
  ``FST (crepSem$evaluate
      (crepLang$StoreByte (crepLang$Const (24w:64 word))
        (crepLang$Const (0xAAw:64 word)), ^s0))``;

val _ = print_eval "storebyte_outside_domain_mem8"
  ``(SND (crepSem$evaluate
      (crepLang$StoreByte (crepLang$Const (24w:64 word))
        (crepLang$Const (0xAAw:64 word)), ^s0))).memory (8w:64 word)``;