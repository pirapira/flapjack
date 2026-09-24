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
val _ = print_eval "mem_load_32_def_little"
  ``mem_load_32 ^mem_little ^dm_little F 0w``;
val _ = print_eval "mem_load_32_def_big"
  ``mem_load_32 ^mem_little ^dm_little T 0w``;
val _ = print_eval "mem_load_32_def_misaligned"
  ``mem_load_32 ^mem_little ^dm_little F 1w``;
val _ = print_eval "mem_load_32_def_missing"
  ``mem_load_32 ^mem_little ({} : 64 word set) F 0w``;

(* Structured mem_load_def rows: One/Comb/Named over a small struct context. *)
val mem0 = ``(\a:64 word.
  if a = 0w then Word (0x11w:64 word)
  else if a = 8w then Word (0x22w:64 word) else ARB) : 64 word -> 64 word_lab``;
val dm0 = ``{0w;8w} : 64 word set``;
val no_stcs = ``[] : (mlstring # panLang$struct_info) list``;
val stcs_s = ``[(strlit "S", <| fields := [(strlit "f", One)]; size := 3 |>)]
  : (mlstring # panLang$struct_info) list``;
val _ = print_eval "mem_load_def_one_hit" ``mem_load One 0w ^dm0 ^mem0 ^no_stcs``;
val _ = print_eval "mem_load_def_one_miss" ``mem_load One 0w ({} : 64 word set) ^mem0 ^no_stcs``;
val _ = print_eval "mem_load_def_comb_pair" ``mem_load (Comb [One; One]) 0w ^dm0 ^mem0 ^no_stcs``;
val _ = print_eval "mem_load_def_named_found" ``mem_load (Named (strlit "S")) 0w ^dm0 ^mem0 ^stcs_s``;
val _ = print_eval "mem_load_def_named_missing" ``mem_load (Named (strlit "T")) 0w ^dm0 ^mem0 ^stcs_s``;


(* width-24 alignment check: HOL byte_align clears LOG2(24/8)=1 low bit, so
   5w aligns to 4w (division by 3 would give 3w). *)
val mem24 = ``(\a:24 word. if a = 4w then Word (0x112233w:24 word) else ARB)
  : 24 word -> 24 word_lab``;
val dm24 = ``{4w} : 24 word set``;
val _ = print_eval "mem_load_byte_def_w24_addr5"
  ``mem_load_byte ^mem24 ^dm24 F (5w:24 word)``;
val _ = print_eval "mem_load_32_def_w24_addr4"
  ``mem_load_32 ^mem24 ^dm24 F (4w:24 word)``;

(* NStruct rows: field-name equality and the shape_of field check. *)
val stcs_pair = ``[(strlit "Pair", <| fields := [(strlit "f", One)]; size := 1 |>)]
  : (mlstring # panLang$struct_info) list``;
val with_pair = ``(^little with structs := ^stcs_pair)``;
val _ = print_eval "nstruct_ok"
  ``eval ^with_pair (panLang$NStruct (strlit "Pair") [(strlit "f", panLang$Const 7w)])``;
val _ = print_eval "nstruct_shape_mismatch"
  ``eval ^with_pair (panLang$NStruct (strlit "Pair") [(strlit "f", panLang$RStruct [])])``;
val _ = print_eval "nstruct_name_mismatch"
  ``eval ^with_pair (panLang$NStruct (strlit "Pair") [(strlit "g", panLang$Const 7w)])``;
val _ = print_eval "nstruct_missing_struct"
  ``eval ^little (panLang$NStruct (strlit "Pair") [(strlit "f", panLang$Const 7w)])``;

val _ = print_eval "pan_sem_state_eval_done" ``0``;
