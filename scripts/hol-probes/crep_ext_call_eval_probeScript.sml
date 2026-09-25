(* Direct Cake/HOL observations for the ExtCall clause of crepSem evaluate. *)
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

val returning_ffi =
  ``<| oracle := (λname:ffi$ffiname. λst:unit. λconf:word8 list.
        λbytes:word8 list.
        ffi$Oracle_return st (MAP (λb:word8. 0x2aw) bytes));
      ffi_state := (); io_events := [] |>``;
val final_ffi =
  ``<| oracle := (λname:ffi$ffiname. λst:unit. λconf:word8 list.
        λbytes:word8 list. ffi$Oracle_final ffi$FFI_diverged);
      ffi_state := (); io_events := [] |>``;

val s =
  ``(<| locals := (FEMPTY |+ (0, Word (1w:64 word))
                    |+ (1, Word (0w:64 word))
                    |+ (2, Word (1w:64 word))
                    |+ (3, Word (8w:64 word)));
        globals := FEMPTY;
        code := FEMPTY;
        memory := K (Word (0w:64 word));
        memaddrs := UNIV;
        sh_memaddrs := {};
        clock := 5;
        be := F;
        ffi := ^returning_ffi;
        base_addr := (0w:64 word);
        top_addr := (100w:64 word) |> : (64, unit) crepSem$state)``;
val s_final = ``^s with ffi := ^final_ffi``;
val s_missing_length = ``^s with locals := (FEMPTY |+ (1, Word (0w:64 word))
                                             |+ (2, Word (1w:64 word))
                                             |+ (3, Word (8w:64 word)))``;
val s_read_error = ``^s with memaddrs := {}``;

val _ = print_eval "extcall_return_eval"
  ``case evaluate ((ExtCall «f» 1 0 3 2) : 64 crepLang$prog, ^s) of
      (NONE, post) =>
        post.memory (8w:64 word) = Word (0x2aw:64 word) /\
        LENGTH post.ffi.io_events = 1 /\
        (case post.ffi.io_events of
         | [ffi$IO_event name conf pairs] =>
             name = ffi$ExtCall «f» /\ conf = [0w] /\
             MAP FST pairs = [0w] /\ MAP SND pairs = [0x2aw]
         | _ => F)
    | _ => F``;

val _ = print_eval "extcall_final_eval"
  ``case evaluate ((ExtCall «live» 1 0 3 2) : 64 crepLang$prog, ^s_final) of
      (SOME (FinalFFI (ffi$Final_event name conf bytes outcome)), post) =>
        name = ffi$ExtCall «live» /\ conf = [0w] /\ bytes = [0w] /\
        outcome = ffi$FFI_diverged /\
        FLOOKUP post.locals 0 = SOME (Word (1w:64 word)) /\
        LENGTH post.ffi.io_events = 0
    | _ => F``;

val _ = print_eval "extcall_missing_local_eval"
  ``case evaluate ((ExtCall «f» 1 0 3 2) : 64 crepLang$prog,
       ^s_missing_length) of
      (SOME Error, post) =>
        FLOOKUP post.locals 0 = NONE /\ LENGTH post.ffi.io_events = 0
    | _ => F``;

val _ = print_eval "extcall_read_error_eval"
  ``case evaluate ((ExtCall «f» 1 0 3 2) : 64 crepLang$prog,
       ^s_read_error) of
      (SOME Error, post) =>
        FLOOKUP post.locals 0 = SOME (Word (1w:64 word)) /\
        LENGTH post.ffi.io_events = 0
    | _ => F``;
