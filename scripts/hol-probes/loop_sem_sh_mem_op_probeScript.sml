(*
  Direct HOL-EVAL fixture for Pancake loopSem sh_mem_op_def.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:255-262.
  The fixture observes the byte-count configuration selected by each source
  load/store operator after a successful mapped-memory FFI call.
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
val source_state =
  ``(^s with <| locals := insert 1 (Word (7w : 8 word)) LN;
      sh_mdomain := {3w}; ffi := ^returning_ffi |>)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "load"
  ``case loopSem$sh_mem_op Load 1 (3w : 8 word) ^source_state of
      (res,s') => case s'.ffi.io_events of
        [IO_event _ conf _] => conf | _ => []``
val _ = print_eval "store"
  ``case loopSem$sh_mem_op Store 1 (3w : 8 word) ^source_state of
      (res,s') => case s'.ffi.io_events of
        [IO_event _ conf _] => conf | _ => []``
val _ = print_eval "load8"
  ``case loopSem$sh_mem_op Load8 1 (3w : 8 word) ^source_state of
      (res,s') => case s'.ffi.io_events of
        [IO_event _ conf _] => conf | _ => []``
val _ = print_eval "store8"
  ``case loopSem$sh_mem_op Store8 1 (3w : 8 word) ^source_state of
      (res,s') => case s'.ffi.io_events of
        [IO_event _ conf _] => conf | _ => []``
val _ = print_eval "load16"
  ``case loopSem$sh_mem_op Load16 1 (3w : 8 word) ^source_state of
      (res,s') => case s'.ffi.io_events of
        [IO_event _ conf _] => conf | _ => []``
val _ = print_eval "store16"
  ``case loopSem$sh_mem_op Store16 1 (3w : 8 word) ^source_state of
      (res,s') => case s'.ffi.io_events of
        [IO_event _ conf _] => conf | _ => []``
val _ = print_eval "load32"
  ``case loopSem$sh_mem_op Load32 1 (3w : 8 word) ^source_state of
      (res,s') => case s'.ffi.io_events of
        [IO_event _ conf _] => conf | _ => []``
val _ = print_eval "store32"
  ``case loopSem$sh_mem_op Store32 1 (3w : 8 word) ^source_state of
      (res,s') => case s'.ffi.io_events of
        [IO_event _ conf _] => conf | _ => []``
