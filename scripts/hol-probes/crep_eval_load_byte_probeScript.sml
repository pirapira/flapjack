(*
  Direct HOL observations for the crepSem LoadByte evaluator case.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:90-137 (`eval_def`),
  :104-108 (`eval s (LoadByte addr) = ... mem_load_byte s.memory s.memaddrs
  s.be w`), and cakeml/pancake/semantics/panSemScript.sml:86-92
  (`mem_load_byte_def`).  The memory cell holds the 64-bit word
  0x1122334455667788 at address 8 and `memaddrs = {8w}`.  Little-endian byte
  order gives 0x88 at address 8 and 0x77 at address 9; an address outside
  `memaddrs` yields NONE.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(64,unit) crepSem$state)``;
val s0 = ``(^s with <|
    memory := (\(a : 64 word).
      if a = (8w:64 word) then Word (0x1122334455667788w:64 word)
      else Word (0w:64 word));
    memaddrs := {(8w:64 word)};
    be := F |>)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "eval_loadbyte_addr8"
  ``crepSem$eval ^s0 (crepLang$LoadByte (crepLang$Const (8w:64 word)))``;

val _ = print_eval "eval_loadbyte_addr9"
  ``crepSem$eval ^s0 (crepLang$LoadByte (crepLang$Const (9w:64 word)))``;

val _ = print_eval "eval_loadbyte_addr10"
  ``crepSem$eval ^s0 (crepLang$LoadByte (crepLang$Const (10w:64 word)))``;

val _ = print_eval "eval_loadbyte_outside_domain"
  ``crepSem$eval ^s0 (crepLang$LoadByte (crepLang$Const (24w:64 word)))``;

val _ = print_eval "mem_load_byte_addr9"
  ``panSem$mem_load_byte
      (\(a : 64 word). if a = (8w:64 word)
         then Word (0x1122334455667788w:64 word) else Word (0w:64 word))
      {(8w:64 word)} F (9w:64 word)``;