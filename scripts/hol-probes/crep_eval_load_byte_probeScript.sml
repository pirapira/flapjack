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
(* A width-24 source-word state exercises HOL byte_align's non-power-of-two
   boundary: dimindex DIV 8 is 3, LOG2 3 is 1, so address 5 aligns to 4. *)
val s24 = ``(s:(24,unit) crepSem$state) with <|
    memory := (\(a : 24 word).
      if a = (4w:24 word) then Word (0x332211w:24 word)
      else Word (0w:24 word));
    memaddrs := {(4w:24 word)};
    be := F |>``;
val s24BE = ``(^s24 with be := T)``;

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

val _ = print_eval "eval_loadbyte_w24_addr5"
  ``crepSem$eval ^s24
      (crepLang$LoadByte (crepLang$Const (5w:24 word)))``;

val _ = print_eval "eval_loadbyte_w24_be_addr5"
  ``crepSem$eval ^s24BE
      (crepLang$LoadByte (crepLang$Const (5w:24 word)))``;
