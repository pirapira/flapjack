(* Direct HOL-EVAL observations for the FFI byte-codec boundary that the Crep
   runtime ffiContext must respect.

   References:
     HOL/src/n-bit/byteScript.sml: bytes_in_word, get_byte, set_byte,
       word_to_bytes, word_of_bytes
     HOL/src/n-bit/alignmentScript.sml: byte_align
     pancake/semantics/panSemScript.sml: shared-memory and ExtCall byte codec
   For the 64-bit RISC-V target, bytes_in_word = 8w and byte_align clears the
   low three bits. *)
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

val w = ``(0x0102030405060708w:64 word)``;

val _ = print_eval "bytes64" ``(bytes_in_word : 64 word)``;
val _ = print_eval "get_byte_0" ``get_byte (0w:64 word) ^w F``;
val _ = print_eval "get_byte_1" ``get_byte (1w:64 word) ^w F``;
val _ = print_eval "get_byte_7" ``get_byte (7w:64 word) ^w F``;
val _ = print_eval "byte_align_8" ``byte_align (9w:64 word)``;
val _ = print_eval "byte_align_16" ``byte_align (16w:64 word)``;
val _ = print_eval "word_to_bytes_64" ``word_to_bytes ^w F``;
val _ = print_eval "word_of_bytes_roundtrip"
  ``word_of_bytes F (0w:64 word) (word_to_bytes ^w F)``;
val _ = print_eval "set_byte_0_roundtrip"
  ``set_byte (0w:64 word) (get_byte (0w:64 word) ^w F) ^w F``;
