(*
  Direct HOL-EVAL fixture for Pancake loopSem sh_mem_load_def.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:198-215.
  The successful case uses a return-valued SharedMem/MappedRead oracle and
  observes the destination local plus the appended FFI event; failure cases
  observe source Error behavior before the oracle boundary.
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
        | ffi$SharedMem ffi$MappedRead => ffi$Oracle_return st bytes
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

val _ = print_eval "return_zero_width"
  ``case loopSem$sh_mem_load 1 (3w : 8 word) 0
      (^s with <| locals := insert 1 (Word (0w : 8 word)) LN;
                  sh_mdomain := {3w}; ffi := ^returning_ffi |>) of
      (res,s') => (res, (case lookup 1 s'.locals of
        SOME (Word w) => w = 3w | _ => F), LENGTH s'.ffi.io_events)``
val _ = print_eval "missing_local_inserts"
  ``case loopSem$sh_mem_load 1 (3w : 8 word) 0
      (^s with <| locals := LN; sh_mdomain := {3w}; ffi := ^returning_ffi |>) of
      (res,s') => (res, (case lookup 1 s'.locals of
        SOME (Word w) => w = 3w | _ => F))``
val _ = print_eval "domain_error"
  ``case loopSem$sh_mem_load 1 (4w : 8 word) 0
      (^s with <| locals := insert 1 (Word (0w : 8 word)) LN;
                  sh_mdomain := {3w}; ffi := ^returning_ffi |>) of
      (res,s') => (res, (case lookup 1 s'.locals of
        SOME (Word w) => w = 3w | _ => F))``
val _ = print_eval "aligned_domain_original_payload"
  ``case loopSem$sh_mem_load 1 (3w : 32 word) 1
      (^s32 with <| locals := LN; sh_mdomain := {0w}; ffi := ^returning_ffi |>) of
      (res,s') => (res,
        case lookup 1 s'.locals of SOME (Word w) => w2n w | _ => 0)``
val _ = print_eval "byte_align_three"
  ``byte_align (3w : 32 word)``
