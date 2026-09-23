(* Direct HOL-EVAL observations for the shared-memory address validity
   predicate that the Crep runtime must respect.

   References:
     cakeml/pancake/semantics/panSemScript.sml:510-524
       sh_mem_load checks `addr IN s.sh_memaddrs` for width 0 and
       `byte_align addr IN s.sh_memaddrs` for nonzero widths
     cakeml/pancake/semantics/crepSemScript.sml:168-204 (same guard)
     src/n-bit/alignmentScript.sml: byte_align = align (LOG2 (dimindex DIV 8))
   For the 64-bit target byte_align clears the low three bits, so 9w aligns
   to 8w while 16w stays 16w. *)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val s = ``{8w : 64 word}``;

val _ = print_eval "valid_zero_mem" ``(8w:64 word) IN ^s``;
val _ = print_eval "valid_zero_out" ``(9w:64 word) IN ^s``;
val _ = print_eval "valid_aligned_mem" ``(byte_align (9w:64 word)) IN ^s``;
val _ = print_eval "valid_aligned_out" ``(byte_align (16w:64 word)) IN ^s``;
val _ = print_eval "align_9" ``(byte_align (9w:64 word))``;
val _ = print_eval "align_16" ``(byte_align (16w:64 word))``;
