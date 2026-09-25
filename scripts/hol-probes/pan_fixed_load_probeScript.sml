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
val _ = print_thm "byte_align_definition" alignmentTheory.byte_align_def;
val _ = print_thm "aligned_definition" alignmentTheory.aligned_def;
val _ = print_thm "align_definition" alignmentTheory.align_def;
val _ = print_thm "get_byte_definition" byteTheory.get_byte_def;
val _ = print_thm "byte_index_definition" byteTheory.byte_index_def;
val _ = print_thm "word_of_bytes_definition" byteTheory.word_of_bytes_def;

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
val _ = print_eval "load32_unaligned_width1_address1"
  ``mem_load_32 (\a : 1 word. Word (1w : 1 word))
      UNIV F (1w : 1 word)``
val _ = print_eval "aligned_width1_address1"
  ``aligned 2 (1w : 1 word)``
val _ = print_eval "byte_align_width1_address1"
  ``byte_align (1w : 1 word)``
val _ = print_eval "byte_align_width24_address5"
  ``byte_align (5w : 24 word)``
val _ = print_eval "byte_load_width24_address5"
  ``mem_load_byte (\a : 24 word. Word (0x332211w : 24 word))
      {4w} F 5w``
val _ = print_eval "byte_load_width24_address5_big_endian"
  ``mem_load_byte (\a : 24 word. Word (0x332211w : 24 word))
      {4w} T 5w``
val _ = print_eval "byte_load_width4_address1"
  ``mem_load_byte (\a : 4 word. Word (1w : 4 word))
      UNIV F 1w``
val _ = print_eval "byte_load_width4_address0_nonzero_little_endian"
  ``mem_load_byte (\a : 4 word. Word (0xBw : 4 word))
      UNIV F 0w``
val _ = print_eval "byte_load_width4_address1_nonzero_little_endian"
  ``mem_load_byte (\a : 4 word. Word (0xBw : 4 word))
      UNIV F 1w``
val _ = print_eval "byte_load_width4_address0_nonzero_big_endian"
  ``mem_load_byte (\a : 4 word. Word (0xBw : 4 word))
      UNIV T 0w``
val _ = print_eval "byte_load_width4_address1_nonzero_big_endian"
  ``mem_load_byte (\a : 4 word. Word (0xBw : 4 word))
      UNIV T 1w``
val _ = print_eval "load32_width4_address0_nonzero_little_endian"
  ``mem_load_32 (\a : 4 word. Word (0xBw : 4 word))
      UNIV F 0w``
val _ = print_eval "load32_width4_address0_nonzero_big_endian"
  ``mem_load_32 (\a : 4 word. Word (0xBw : 4 word))
      UNIV T 0w``
val _ = print_eval "word_of_bytes_width4_little_endian_expected"
  ``word_of_bytes F (0w:word32) [0xBw:word8; 0w; 0w; 0w]``
val _ = print_eval "word_of_bytes_width4_big_endian_expected"
  ``word_of_bytes T (0w:word32) [0xBw:word8; 0xBw; 0xBw; 0xBw]``
val _ = print_eval "word_of_bytes_width32_distinct_little"
  ``word_of_bytes F (0w:word32) [0x11w:word8; 0x22w; 0x33w; 0x44w]``
val _ = print_eval "word_of_bytes_width32_distinct_big"
  ``word_of_bytes T (0w:word32) [0x11w:word8; 0x22w; 0x33w; 0x44w]``
val _ = print_eval "byte_align_width4_address1"
  ``byte_align (1w : 4 word)``
val _ = print_eval "byte_index_width4_address1"
  ``byte_index (1w : 4 word) F``
val _ = print_eval "get_byte_width4_address1"
  ``get_byte (1w : 4 word) (1w : 4 word) F``
val _ = print_eval "get_byte_width4_zero_equation"
  ``get_byte (1w : 4 word) (1w : 4 word) F = (0w : 8 word)``
val _ = print_eval "load32_width24_address4"
  ``mem_load_32 (\a : 24 word. Word (0x332211w : 24 word))
      {4w} F 4w``
