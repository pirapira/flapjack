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
val _ = print_eval "op_add_empty"
  ``eval ^little (panLang$Op Add [])``;
val _ = print_eval "op_add_one"
  ``eval ^little (panLang$Op Add [panLang$Const 1w])``;
val _ = print_eval "op_add_pair"
  ``eval ^little (panLang$Op Add [panLang$Const 1w; panLang$Const 2w])``;
val _ = print_eval "op_and_three"
  ``eval ^little (panLang$Op And [panLang$Const 15w; panLang$Const 6w;
      panLang$Const 3w])``;
val _ = print_eval "op_or_three"
  ``eval ^little (panLang$Op Or [panLang$Const 1w; panLang$Const 2w;
      panLang$Const 4w])``;
val _ = print_eval "op_xor_three"
  ``eval ^little (panLang$Op Xor [panLang$Const 1w; panLang$Const 2w;
      panLang$Const 4w])``;
val _ = print_eval "op_sub_empty"
  ``eval ^little (panLang$Op Sub [])``;
val _ = print_eval "op_sub_pair"
  ``eval ^little (panLang$Op Sub [panLang$Const 3w; panLang$Const 5w])``;
val mem_little =
  ``(\a:64 word. if a = 0w then Word ^word_value else ARB) : 64 word -> 64 word_lab``;
val dm_little = ``{0w} : 64 word set``;
val _ = print_eval "mem_load_byte_def_little_first"
  ``mem_load_byte ^mem_little ^dm_little F 0w``;
val _ = print_eval "mem_load_byte_def_little_last"
  ``mem_load_byte ^mem_little ^dm_little F 7w``;
val _ = print_eval "mem_load_byte_def_big_first"
  ``mem_load_byte ^mem_little ^dm_little T 0w``;
val _ = print_eval "mem_load_byte_def_missing"
  ``mem_load_byte ^mem_little ({} : 64 word set) F 0w``;
val _ = print_eval "pan_sem_state_eval_done" ``0``;
