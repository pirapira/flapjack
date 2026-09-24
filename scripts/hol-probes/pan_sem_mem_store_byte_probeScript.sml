load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

val mem = ``(λw:8 word. Word (0x0807060504030201w:8 word))``;
val dm12 = ``{1w:8 word; 2w:8 word}``;
val dm2 = ``{2w:8 word}``;

val _ = print_eval "store_byte_hit_some"
  (``case mem_store_byte ^mem ^dm12 F (1w:8 word) (0xABw:word8) of
        SOME _ => T
      | NONE => F``);

val _ = print_eval "store_byte_out"
  (``(mem_store_byte ^mem ^dm2 F (1w:8 word) (0xABw:word8) = NONE)``);

val _ = print_eval "store_byte_other_unchanged"
  (``case mem_store_byte ^mem ^dm12 F (1w:8 word) (0xABw:word8) of
        SOME m => (m (3w:8 word) = ^mem (3w:8 word))
      | NONE => F``);

val _ = print_eval "write_bytearray_changed"
  (``((write_bytearray (1w:8 word) [0x11w; 0x22w] ^mem ^dm12 F) (1w:8 word)
        = Word (set_byte (1w:8 word) (0x11w:word8) (0x0807060504030201w:8 word) F))``);

val _ = print_eval "write_bytearray_other_unchanged"
  (``((write_bytearray (1w:8 word) [0x11w; 0x22w] ^mem ^dm12 F) (3w:8 word)
        = ^mem (3w:8 word))``);

val _ = print_eval "write_bytearray_out_of_domain"
  (``((write_bytearray (5w:8 word) [0x11w] ^mem ^dm12 F) (1w:8 word)
        = ^mem (1w:8 word))``);
