(* Direct HOL-EVAL probes for CakeML Pancake fixed-width memory loads. *)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_thm label th =
  (
    print (label ^ "=");
    print_term (concl th);
    print "\n"
  )

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_thm "mem_load_byte_definition" panSemTheory.mem_load_byte_def;
val _ = print_thm "mem_load_32_definition" panSemTheory.mem_load_32_def;

val _ = print_eval "byte_hit"
  ``mem_load_byte (\a : 64 word. Word 0x0807060504030201w)
      {8w} F 9w``
val _ = print_eval "byte_miss"
  ``mem_load_byte (\a : 64 word. Word 0x0807060504030201w)
      {16w} F 9w``
val _ = print_eval "byte_big_endian"
  ``mem_load_byte (\a : 64 word. Word 0x0807060504030201w)
      {8w} T 9w``
val _ = print_eval "load32_hit"
  ``mem_load_32 (\a : 64 word. Word 0x0807060504030201w)
      {8w} F 8w``
val _ = print_eval "load32_unaligned"
  ``mem_load_32 (\a : 64 word. Word 0x0807060504030201w)
      {8w} F 9w``
val _ = print_eval "load32_domain_miss"
  ``mem_load_32 (\a : 64 word. Word 0x0807060504030201w)
      {16w} F 8w``
val _ = print_eval "load32_big_endian"
  ``mem_load_32 (\a : 64 word. Word 0x0807060504030201w)
      {8w} T 8w``
val _ = print_eval "byte_hit_width8"
  ``mem_load_byte (\a : 8 word. Word (0xa5w : 8 word))
      {0w} F 0w``
val _ = print_eval "load32_hit_width8"
  ``mem_load_32 (\a : 8 word. Word (0xa5w : 8 word))
      {0w} F 0w``
