(* Direct HOL-EVAL observations for the target word/byte boundary that the
   Crep runtime must respect.

   References:
     byteScript.sml: byte$bytes_in_word = n2w (dimindex (:'a) DIV 8)
     panSemScript.sml:86-106: mem_load_byte / mem_load_32
   For the 64-bit RISC-V target bytes_in_word = n2w (64 DIV 8) = 8w. *)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val mem =
  ``(λw:64 word. if w = 8w then Word (0x0807060504030201w:64 word)
     else Word (0w:64 word))``;
val dm = ``{8w : 64 word}``;

val _ = print_eval "bytes64" ``(bytes_in_word : 64 word)``;
val _ = print_eval "bytes32" ``(bytes_in_word : 32 word)``;

val _ = print_eval "byte_at_9"
  ``mem_load_byte ^mem ^dm F (9w:64 word)``;
val _ = print_eval "byte_at_8"
  ``mem_load_byte ^mem ^dm F (8w:64 word)``;
val _ = print_eval "byte_outside_domain"
  ``mem_load_byte ^mem ^dm F (16w:64 word)``;

val _ = print_eval "word32_at_8"
  ``mem_load_32 ^mem ^dm F (8w:64 word)``;
val _ = print_eval "word32_unaligned"
  ``mem_load_32 ^mem ^dm F (9w:64 word)``;

val _ = print_eval "store_byte_roundtrip"
  ``case mem_store_byte ^mem ^dm F (8w:64 word) (0xABw:word8) of
      NONE => NONE
    | SOME m2 => mem_load_byte m2 ^dm F (8w:64 word)``;
val _ = print_eval "store_byte_outside"
  ``mem_store_byte ^mem ^dm F (16w:64 word) (0xABw:word8)``;

val _ = print_eval "store32_roundtrip"
  ``case mem_store_32 ^mem ^dm F (8w:64 word) (0xAABBCCDDw:word32) of
      NONE => NONE
    | SOME m2 => mem_load_32 m2 ^dm F (8w:64 word)``;
val _ = print_eval "store32_unaligned"
  ``mem_store_32 ^mem ^dm F (9w:64 word) (0xAABBCCDDw:word32)``;
val _ = print_eval "store32_outside"
  ``mem_store_32 ^mem ^dm F (16w:64 word) (0xAABBCCDDw:word32)``;
