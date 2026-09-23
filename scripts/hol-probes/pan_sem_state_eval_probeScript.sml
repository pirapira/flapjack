(* Direct HOL-EVAL probes for panSem$eval's word and byte load branches. *)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val s = ``(s:(64,unit) panSem$state)``;
val word_value = ``0x1122334455667788w:64 word``;
val little = ``(^s with <|
  locals := FEMPTY; globals := FEMPTY; structs := [];
  memory := (\a:64 word. if a = 0w then Word ^word_value else ARB);
  memaddrs := {0w}; sh_memaddrs := {0w}; be := F |>)``;
val big = ``(^little with be := T)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "word_load_hit"
  ``eval ^little (panLang$Load One (panLang$Const 0w))``;
val _ = print_eval "word_load_miss"
  ``eval (^little with memaddrs := {})
      (panLang$Load One (panLang$Const 0w))``;
val _ = print_eval "byte_little_first"
  ``eval ^little (panLang$LoadByte (panLang$Const 0w))``;
val _ = print_eval "byte_little_last"
  ``eval ^little (panLang$LoadByte (panLang$Const 7w))``;
val _ = print_eval "word32_little"
  ``eval ^little (panLang$Load32 (panLang$Const 0w))``;
val _ = print_eval "byte_big_first"
  ``eval ^big (panLang$LoadByte (panLang$Const 0w))``;
val _ = print_eval "byte_big_last"
  ``eval ^big (panLang$LoadByte (panLang$Const 7w))``;
val _ = print_eval "word32_big"
  ``eval ^big (panLang$Load32 (panLang$Const 0w))``;
val _ = print_eval "op_add_fold_three"
  ``eval ^little (panLang$Op Add [panLang$Const 1w; panLang$Const 2w;
      panLang$Const 3w])``;
val _ = print_eval "op_sub_wrong_arity"
  ``eval ^little (panLang$Op Sub [panLang$Const 1w])``;
