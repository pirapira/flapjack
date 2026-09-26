(*
  Direct HOL observations for the crepSem Load32 evaluator case.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:90-137 (`eval_def`,
  `eval s (Load32 addr) = ... mem_load_32 s.memory s.memaddrs s.be w`), and
  cakeml/pancake/semantics/panSemScript.sml:94-104 (`mem_load_32_def`).  The
  memory cell holds the 64-bit word 0x1122334455667788 at address 8 and
  `memaddrs = {8w}`.  Little-endian Load32 at address 8 reads the low four
  bytes 0x88,0x77,0x66,0x55; address 12 reads 0x44,0x33,0x22,0x11; address 9
  is unaligned (NONE); address 24 is outside `memaddrs` (NONE).  The
  big-endian state reverses the byte order.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(64,unit) crepSem$state)``;
val sLE = ``(^s with <|
    memory := (\(a : 64 word).
      if a = (8w:64 word) then Word (0x1122334455667788w:64 word)
      else Word (0w:64 word));
    memaddrs := {(8w:64 word)};
    be := F |>)``;
val sBE = ``(^s with <|
    memory := (\(a : 64 word).
      if a = (8w:64 word) then Word (0x1122334455667788w:64 word)
      else Word (0w:64 word));
    memaddrs := {(8w:64 word)};
    be := T |>)``;
(* At width 24, Cake's source byte alignment rounds address 5 to 4 because
   LOG2 (dimindex DIV 8) = LOG2 3 = 1. Load32 at aligned address 4 reads
   four source bytes and then returns a 24-bit word. *)
val s24 = ``(s:(24,unit) crepSem$state) with <|
    memory := (\(a : 24 word).
      if a = (4w:24 word) then Word (0x332211w:24 word)
      else Word (0w:24 word));
    memaddrs := {(4w:24 word)};
    be := F |>``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "eval_load32_le_addr8"
  ``crepSem$eval ^sLE (crepLang$Load32 (crepLang$Const (8w:64 word)))``;

val _ = print_eval "eval_load32_le_addr12"
  ``crepSem$eval ^sLE (crepLang$Load32 (crepLang$Const (12w:64 word)))``;

val _ = print_eval "eval_load32_le_unaligned"
  ``crepSem$eval ^sLE (crepLang$Load32 (crepLang$Const (9w:64 word)))``;

val _ = print_eval "eval_load32_le_outside_domain"
  ``crepSem$eval ^sLE (crepLang$Load32 (crepLang$Const (24w:64 word)))``;

val _ = print_eval "eval_load32_be_addr8"
  ``crepSem$eval ^sBE (crepLang$Load32 (crepLang$Const (8w:64 word)))``;

val _ = print_eval "eval_load32_w24_addr4"
  ``crepSem$eval ^s24 (crepLang$Load32 (crepLang$Const (4w:24 word)))``;
