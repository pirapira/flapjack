(*
  Direct HOL-EVAL fixture for the whole-state loopSem memory and shared-memory
  helpers exercised by Flapjack/Test/LoopSemStateParity.lean.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:57-69 and :198-243.

  Rows are chosen so each output is a concrete value that distinguishes the
  Option cases directly:
    - memory rows print the raw loopSem$mem_load result (SOME (Word w) / NONE)
      and the raw updated memory entries (Word w), never a collapsed default.
    - shared-memory rows print the concrete loaded/stored words and the
      io_events length, not a symbolic equality.
  returning_ffi returns for both SharedMem MappedRead and MappedWrite, so the
  store row exercises the FFI_return branch (only ffi is updated, locals kept);
  final_ffi exercises the FFI_final branch (FinalFFI, locals cleared via
  call_env []).
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(8,unit) loopSem$state)``;
val returning_ffi =
  ``<| oracle := (λname. λst. λconf. λbytes.
        case name of
        | ffi$SharedMem ffi$MappedRead => ffi$Oracle_return st bytes
        | ffi$SharedMem ffi$MappedWrite => ffi$Oracle_return st bytes
        | _ => ffi$Oracle_final ffi$FFI_failed);
      ffi_state := ();
      io_events := [] |>``;
val final_ffi =
  ``<| oracle := (λname. λst. λconf. λbytes. ffi$Oracle_final ffi$FFI_failed);
      ffi_state := ();
      io_events := [] |>``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val mem_state =
  ``(^s with <| memory := (0w =+ Word 7w) ((1w =+ Word 2w) (K (Word 0w)));
                mdomain := {0w; 1w} |>)``;

(* Raw Option result: hit is SOME (Word 7w), miss is NONE. *)
val _ = print_eval "ws_mem_load_hit"
  ``loopSem$mem_load (0w : 8 word) ^mem_state``

val _ = print_eval "ws_mem_load_miss"
  ``loopSem$mem_load (5w : 8 word) ^mem_state``

(* Store at 0w of Word 7w; observe both updated (0w) and untouched (1w) entries. *)
val _ = print_eval "ws_mem_store_update"
  ``case loopSem$mem_store (0w : 8 word) (Word 7w) ^mem_state of
      SOME s' => (s'.memory (0w : 8 word), s'.memory (1w : 8 word))
    | NONE => (Word 0w, Word 0w)``

(* Returning MappedRead: result NONE, local 1 set to Word 3w, one io_event.
   The loaded word is printed through `w2n` because EVAL leaves
   `word_of_bytes F 0w [3w]` as an unreduced `set_byte` term; `w2n` forces the
   concrete value, as in loop_sem_sh_mem_load_probe.out. *)
val _ = print_eval "ws_sh_mem_load_return"
  ``case loopSem$sh_mem_load 1 (3w : 8 word) 0
      (^s with <| locals := insert 1 (Word (0w : 8 word)) LN;
                  sh_mdomain := {3w}; ffi := ^returning_ffi |>) of
      (res,s') => (res, (case lookup 1 s'.locals of SOME (Word w) => w2n w | _ => 0),
                   LENGTH s'.ffi.io_events)``

(* Final MappedRead: FinalFFI, locals cleared. *)
val _ = print_eval "ws_sh_mem_load_final"
  ``case loopSem$sh_mem_load 1 (3w : 8 word) 0
      (^s with <| locals := insert 1 (Word (0w : 8 word)) LN;
                  sh_mdomain := {3w}; ffi := ^final_ffi |>) of
      (res,s') => (res, (case lookup 1 s'.locals of NONE => T | _ => F))``

(* Returning MappedWrite: result NONE, stored local 1 kept as Word 7w. *)
val _ = print_eval "ws_sh_mem_store_return"
  ``case loopSem$sh_mem_store 1 (3w : 8 word) 0
      (^s with <| locals := insert 1 (Word (7w : 8 word)) LN;
                  sh_mdomain := {3w}; ffi := ^returning_ffi |>) of
      (res,s') => (res, (case lookup 1 s'.locals of SOME (Word w) => w2n w | _ => 0))``

(* Final MappedWrite: FinalFFI, locals cleared. *)
val _ = print_eval "ws_sh_mem_store_final"
  ``case loopSem$sh_mem_store 1 (3w : 8 word) 0
      (^s with <| locals := insert 1 (Word (7w : 8 word)) LN;
                  sh_mdomain := {3w}; ffi := ^final_ffi |>) of
      (res,s') => (res, (case lookup 1 s'.locals of NONE => T | _ => F))``
