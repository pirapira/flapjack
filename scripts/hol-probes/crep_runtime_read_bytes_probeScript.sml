(* Direct HOL-EVAL observations for the byte-array read that feeds
   `call_FFI` in the Crep external-call semantics.

   References:
     cakeml/misc/miscScript.sml:113-121: read_bytearray
     cakeml/pancake/semantics/panSemScript.sml:86-92: mem_load_byte
     cakeml/pancake/semantics/crepSemScript.sml ExtCall: read_bytearray ptr
       (w2n len) (mem_load_byte s.memory s.memaddrs s.be) *)

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
val laod = ``mem_load_byte ^mem ^dm F``;

val _ = print_eval "read_bytes_zero"
  ``read_bytearray (8w:64 word) 0 ^laod``;
val _ = print_eval "read_bytes_short"
  ``read_bytearray (8w:64 word) 4 ^laod``;
val _ = print_eval "read_bytes_cross"
  ``read_bytearray (8w:64 word) 8 ^laod``;
val _ = print_eval "read_bytes_out_of_domain"
  ``read_bytearray (8w:64 word) 9 ^laod``;
