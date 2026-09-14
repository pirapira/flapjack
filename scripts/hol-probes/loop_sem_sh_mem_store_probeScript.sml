(*
  Direct HOL-EVAL fixture for Pancake loopSem sh_mem_store_def.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:217-243.
  The fixture observes successful mapped writes, source errors, and the
  alignment-sensitive original-address payload for nonzero widths.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(8,unit) loopSem$state)``;
val s32 = ``(s:(32,unit) loopSem$state)``;
val returning_ffi =
  ``<| oracle := (λname. λst. λconf. λbytes.
        case name of
        | ffi$SharedMem ffi$MappedWrite => ffi$Oracle_return st bytes
        | _ => ffi$Oracle_final ffi$FFI_failed);
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

val _ = print_eval "store_zero_width"
  ``case loopSem$sh_mem_store 1 (3w : 8 word) 0
      (^s with <| locals := insert 1 (Word (7w : 8 word)) LN;
                  sh_mdomain := {3w}; ffi := ^returning_ffi |>) of
      (res,s') => (res, lookup 1 s'.locals, LENGTH s'.ffi.io_events)``
val _ = print_eval "missing_word_error"
  ``case loopSem$sh_mem_store 1 (3w : 8 word) 0
      (^s with <| locals := LN; sh_mdomain := {3w}; ffi := ^returning_ffi |>) of
      (res,s') => (res, LENGTH s'.ffi.io_events)``
val _ = print_eval "domain_error"
  ``case loopSem$sh_mem_store 1 (4w : 8 word) 0
      (^s with <| locals := insert 1 (Word (7w : 8 word)) LN;
                  sh_mdomain := {3w}; ffi := ^returning_ffi |>) of
      (res,s') => (res, LENGTH s'.ffi.io_events)``
val _ = print_eval "aligned_domain_original_payload"
  ``case loopSem$sh_mem_store 1 (3w : 32 word) 1
      (^s32 with <| locals := insert 1 (Word (171w : 32 word)) LN;
                   sh_mdomain := {0w}; ffi := ^returning_ffi |>) of
      (res,s') =>
        case s'.ffi.io_events of
        | [IO_event _ _ bytes] => bytes =
            [(171w,171w); (3w,3w); (0w,0w); (0w,0w); (0w,0w)]
        | _ => F``
