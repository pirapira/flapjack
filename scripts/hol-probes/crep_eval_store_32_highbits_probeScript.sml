(*
  Direct HOL observations for the crepSem Store32 evaluator case showing that
  only the low 32 bits of the stored 64-bit value are written.  Reference:
  cakeml/pancake/semantics/crepSemScript.sml (`eval_def`/Store32 case) and
  cakeml/pancake/semantics/panSemScript.sml (`mem_store_32_def`, which takes
  `hw : word32` and is applied to `w2w w`).  The memory cell holds
  0x1122334455667788 at address 8 and `memaddrs = {8w}`.  Storing
  0xDEADBEEF11223344 and storing 0x0000000011223344 leave the same cell, namely
  0x1122334411223344; the `w2w` truncation row records the word32 actually
  consumed by `mem_store_32`.
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

val _ = print_eval "w2w_highbits"
  ``(w2w (0xDEADBEEF11223344w:64 word)) : word32``;

val _ = print_eval "store32_highbits_result"
  ``FST (crepSem$evaluate
      (crepLang$Store32 (crepLang$Const (8w:64 word))
        (crepLang$Const (0xDEADBEEF11223344w:64 word)), ^s0))``;

val _ = print_eval "store32_highbits_mem8"
  ``(SND (crepSem$evaluate
      (crepLang$Store32 (crepLang$Const (8w:64 word))
        (crepLang$Const (0xDEADBEEF11223344w:64 word)), ^s0))).memory (8w:64 word)``;

val _ = print_eval "store32_lowbits_mem8"
  ``(SND (crepSem$evaluate
      (crepLang$Store32 (crepLang$Const (8w:64 word))
        (crepLang$Const (0x11223344w:64 word)), ^s0))).memory (8w:64 word)``;

val _ = print_eval "store32_unaligned_result"
  ``FST (crepSem$evaluate
      (crepLang$Store32 (crepLang$Const (9w:64 word))
        (crepLang$Const (0x11223344w:64 word)), ^s0))``;