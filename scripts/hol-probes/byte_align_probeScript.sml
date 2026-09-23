(*
  Direct HOL-EVAL fixture for HOL `byte$byte_align`
  (`/home/zksecurity/HOL/src/n-bit/alignmentScript.sml:23`):
      byte_align (w : 'a word) = align (LOG2 (dimindex(:'a) DIV 8)) w
  i.e. the low `LOG2 (width DIV 8)` bits are cleared.  LoopSem.lean's tagged
  `memLoadByteAuxHOL`/`memStoreByteAuxHOL` use the width-generic
  `riscvByteAlignHOL`, which must match this (not division by `width DIV 8`).
  The width-24 rows pin the non-power-of-two case: `LOG2 3 = 1`, so alignment
  rounds down to a multiple of 2, not 3.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open alignmentTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "ba24_5" ``byte_align (5w:24 word)``
val _ = print_eval "ba24_6" ``byte_align (6w:24 word)``
val _ = print_eval "ba24_7" ``byte_align (7w:24 word)``
val _ = print_eval "ba64_13" ``byte_align (13w:64 word)``
val _ = print_eval "ba8_7" ``byte_align (7w:8 word)``
