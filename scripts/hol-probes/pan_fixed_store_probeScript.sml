(* Direct HOL-EVAL probes for CakeML Pancake fixed-width memory stores. *)
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
  end

val _ = print_eval "byte_store_hit"
  ``(case mem_store_byte (\a : 64 word. Word 0x0807060504030201w)
        {8w} F 9w 0xaaw of
      | SOME m => SOME (m 8w)
      | NONE => NONE)``
val _ = print_eval "byte_store_miss"
  ``(case mem_store_byte (\a : 64 word. Word 0x0807060504030201w)
        {16w} F 9w 0xaaw of
      | SOME m => SOME (m 8w)
      | NONE => NONE)``
val _ = print_eval "store32_hit"
  ``(case mem_store_32 (\a : 64 word. Word 0x0807060504030201w)
        {8w} F 8w 0x11223344w of
      | SOME m => SOME (m 8w)
      | NONE => NONE)``
val _ = print_eval "store32_unaligned"
  ``(case mem_store_32 (\a : 64 word. Word 0x0807060504030201w)
        {8w} F 9w 0x11223344w of
      | SOME m => SOME (m 8w)
      | NONE => NONE)``
