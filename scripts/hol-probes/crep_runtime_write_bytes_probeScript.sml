(* Direct HOL-EVAL observations for the byte-array write-back performed by
   `crepSem$ExtCall` after `call_FFI`.

   References:
     cakeml/misc/miscScript.sml:113-121: read_bytearray
     cakeml/pancake/semantics/panSemScript.sml:300-316: mem_store_byte,
       write_bytearray (total: a failing `mem_store_byte` keeps the memory)
     cakeml/pancake/semantics/crepSemScript.sml ExtCall: write_bytearray ptr
       new_bytes s.memory s.memaddrs s.be *)

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
val eight = ``[0xAAw; 0xBBw; 0xCCw; 0xDDw; 0xEEw; 0xFFw; 0x11w; 0x22w]
  : word8 list``;

val _ = print_eval "write_head"
  ``mem_load_byte (write_bytearray (8w:64 word) ^eight ^mem ^dm F)
     ^dm F (8w:64 word)``;
val _ = print_eval "write_byte1"
  ``mem_load_byte (write_bytearray (8w:64 word) ^eight ^mem ^dm F)
     ^dm F (9w:64 word)``;
val _ = print_eval "write_32"
  ``mem_load_32 (write_bytearray (8w:64 word) ^eight ^mem ^dm F)
     ^dm F (8w:64 word)``;
val _ = print_eval "write_unaligned_byte"
  ``mem_load_byte
     (write_bytearray (9w:64 word) ([0xAAw] : word8 list) ^mem ^dm F)
     ^dm F (9w:64 word)``;
val _ = print_eval "write_out_of_domain"
  ``mem_load_byte
     (write_bytearray (16w:64 word) ([0xAAw] : word8 list) ^mem ^dm F)
     ^dm F (8w:64 word)``;
