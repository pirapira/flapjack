(*
  Direct HOL observations for `panSem$mem_store`, the store used by
  `crepSem$evaluate` (`crepSemScript.sml:267-286`).
  Reference: cakeml/pancake/semantics/panSemScript.sml:373-378

    mem_store (addr:'a word) (w:'a word_lab) dm m =
      if addr IN dm then SOME ((addr =+ w) m) else NONE

  `memory` is a total function of addresses and `memaddrs` is the guard.  A
  valid store updates exactly that address; a store outside `memaddrs` is NONE.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val m0 = ``(\(_ : 8 word). Word (0w : 8 word)) : 8 word -> 8 word_lab``;

val _ = print_eval "mem_store_valid_lookup"
  ``(case panSem$mem_store (0w:8 word) (Word (7w:8 word)) {(0w:8 word)} ^m0 of
      SOME m => SOME (m (0w:8 word))
    | NONE => NONE)``;

val _ = print_eval "mem_store_valid_other"
  ``(case panSem$mem_store (0w:8 word) (Word (7w:8 word)) {(0w:8 word)} ^m0 of
      SOME m => SOME (m (1w:8 word))
    | NONE => SOME (Word (0w:8 word)))``;

val _ = print_eval "mem_store_invalid"
  ``panSem$mem_store (9w:8 word) (Word (7w:8 word)) {(0w:8 word)} ^m0``;
