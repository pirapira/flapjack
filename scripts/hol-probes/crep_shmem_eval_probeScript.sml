(* Direct Cake/HOL observations for the restricted total Crep ShMem clause. *)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val echo_oracle =
  ``(λname:ffi$ffiname. λst:unit. λconf:word8 list. λbytes:word8 list.
      ffi$Oracle_return st bytes)``;

val final_oracle =
  ``((λname:ffi$ffiname. λst:unit. λconf:word8 list. λbytes:word8 list.
      ffi$Oracle_final ffi$FFI_diverged) :
      ffi$ffiname -> unit -> word8 list -> word8 list ->
        unit ffi$oracle_result)``;

val ffi = ``<| oracle := ^echo_oracle; ffi_state := (); io_events := [] |>``;
val final_ffi = ``<| oracle := ^final_oracle; ffi_state := (); io_events := [] |>``;

val s =
  ``(<| locals := (FEMPTY |+ (0, Word (7w:64 word)) |+ (1, Word (0w:64 word)));
        globals := FEMPTY;
        code := FEMPTY;
        memory := K (Word (0w:64 word));
        memaddrs := {};
        sh_memaddrs := {8w; 10w};
        clock := 5;
        be := F;
        ffi := ^ffi;
        base_addr := (0w:64 word);
        top_addr := (100w:64 word) |> : (64, unit) crepSem$state)``;

val s_bad_domain = ``^s with sh_memaddrs := {10w}``;
val s_aligned_domain = ``^s with sh_memaddrs := {8w}``;
val s_final = ``^s with ffi := ^final_ffi``;

val _ = print_eval "shmem_load_success"
  ``case evaluate ((ShMem Load 1 (Const (10w:64 word))) : 64 crepLang$prog, ^s) of
      (NONE, post) =>
        FLOOKUP post.locals 1 = SOME (Word (10w:64 word)) /\
        LENGTH post.ffi.io_events = 1 /\
        (case post.ffi.io_events of
         | [ffi$IO_event name conf pairs] =>
             name = ffi$SharedMem ffi$MappedRead /\ conf = [0w] /\
             MAP FST pairs = word_to_bytes (10w:64 word) F /\
             MAP SND pairs = word_to_bytes (10w:64 word) F
         | _ => F)
    | _ => F``;

val _ = print_eval "shmem_store_success"
  ``case evaluate ((ShMem Store 0 (Const (10w:64 word))) : 64 crepLang$prog, ^s) of
      (NONE, post) =>
        FLOOKUP post.locals 0 = SOME (Word (7w:64 word)) /\
        LENGTH post.ffi.io_events = 1 /\
        (case post.ffi.io_events of
         | [ffi$IO_event name conf pairs] =>
             name = ffi$SharedMem ffi$MappedWrite /\ conf = [0w] /\
             MAP FST pairs = word_to_bytes (7w:64 word) F ++ word_to_bytes (10w:64 word) F /\
             MAP SND pairs = word_to_bytes (7w:64 word) F ++ word_to_bytes (10w:64 word) F
         | _ => F)
    | _ => F``;

val _ = print_eval "shmem_load8_success"
  ``case evaluate ((ShMem Load8 1 (Const (10w:64 word))) : 64 crepLang$prog, ^s_aligned_domain) of
      (NONE, post) =>
        FLOOKUP post.locals 1 = SOME (Word (10w:64 word)) /\
        (case post.ffi.io_events of
         | [ffi$IO_event name conf pairs] =>
             name = ffi$SharedMem ffi$MappedRead /\ conf = [1w] /\
             MAP FST pairs = word_to_bytes (10w:64 word) F /\
             MAP SND pairs = word_to_bytes (10w:64 word) F
         | _ => F)
    | _ => F``;

val _ = print_eval "shmem_store8_success"
  ``case evaluate ((ShMem Store8 0 (Const (10w:64 word))) : 64 crepLang$prog, ^s_aligned_domain) of
      (NONE, post) =>
        FLOOKUP post.locals 0 = SOME (Word (7w:64 word)) /\
        (case post.ffi.io_events of
         | [ffi$IO_event name conf pairs] =>
             name = ffi$SharedMem ffi$MappedWrite /\ conf = [1w] /\ LENGTH pairs = 9 /\
             MAP FST pairs = TAKE 1 (word_to_bytes (7w:64 word) F) ++
               word_to_bytes (10w:64 word) F /\
             MAP SND pairs = TAKE 1 (word_to_bytes (7w:64 word) F) ++
               word_to_bytes (10w:64 word) F
         | _ => F)
    | _ => F``;

val _ = print_eval "shmem_load_domain_error"
  ``case evaluate ((ShMem Load8 1 (Const (10w:64 word))) : 64 crepLang$prog, ^s_bad_domain) of
      (SOME Error, post) =>
        FLOOKUP post.locals 1 = SOME (Word (0w:64 word)) /\ post.ffi.io_events = []
    | _ => F``;

val _ = print_eval "shmem_missing_local_error"
  ``case evaluate ((ShMem Load 9 (Const (10w:64 word))) : 64 crepLang$prog, ^s) of
      (SOME Error, post) =>
        FLOOKUP post.locals 0 = SOME (Word (7w:64 word)) /\ post.ffi.io_events = []
    | _ => F``;

val _ = print_eval "shmem_load_final"
  ``case evaluate ((ShMem Load 1 (Const (10w:64 word))) : 64 crepLang$prog, ^s_final) of
      (SOME (FinalFFI (ffi$Final_event (ffi$SharedMem ffi$MappedRead) _ _ outcome)), post) =>
        outcome = ffi$FFI_diverged /\ FLOOKUP post.locals 0 = NONE
    | _ => F``;
