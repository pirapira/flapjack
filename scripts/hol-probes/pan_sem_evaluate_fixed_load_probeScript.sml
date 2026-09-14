(*
  Direct HOL observations for panSem$eval's fixed-width branches.
  Reference: cakeml/pancake/semantics/panSemScript.sml:247-265,
  with mem_load_byte_def/mem_load_32_def at :86-109.
*)
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

val _ = print_eval "eval_byte_hit"
  ``mem_load_byte (\a : 64 word. Word 0x0807060504030201w)
      {8w} F 9w``;
val _ = print_eval "eval_byte_domain_failure"
  ``mem_load_byte (\a : 64 word. Word 0x0807060504030201w)
      {16w} F 9w``;
val _ = print_eval "eval_load32_hit"
  ``mem_load_32 (\a : 64 word. Word 0x0807060504030201w)
      {8w} F 8w``;
val _ = print_eval "eval_load32_alignment_failure"
  ``mem_load_32 (\a : 64 word. Word 0x0807060504030201w)
      {8w} F 9w``;
