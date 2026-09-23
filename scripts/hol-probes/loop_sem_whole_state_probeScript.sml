(*
  Direct HOL-EVAL fixture for the whole-state loopSem memory and shared-memory
  helpers exercised by Flapjack/Test/LoopSemStateParity.lean.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:57-69 and :198-243.
  The successful shared-memory cases use a return-valued SharedMem/MappedRead
  oracle; the final case uses an Oracle_final oracle.  Failure/update cases
  observe the state directly.
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

val _ = print_eval "ws_mem_load_hit"
  ``case loopSem$mem_load (0w : 8 word)
      (^s with <| memory := (0w =+ Word 7w) (K (Word 0w));
                  mdomain := {0w} |>) of
      SOME (Word w) => w | _ => 0w ``

val _ = print_eval "ws_mem_load_miss"
  ``case loopSem$mem_load (1w : 8 word)
      (^s with <| memory := (0w =+ Word 7w) (K (Word 0w));
                  mdomain := {0w} |>) of
      SOME (Word w) => w | _ => 0w ``

val _ = print_eval "ws_mem_store_update"
  ``case loopSem$mem_store (0w : 8 word) (Word 7w)
      (^s with <| memory := (0w =+ Word 1w) (1w =+ Word 2w) (K (Word 0w));
                  mdomain := {0w; 1w} |>) of
      SOME s' => (case s'.memory (1w : 8 word) of Word w => w | _ => 0w)
    | NONE => 0w ``

val _ = print_eval "ws_sh_mem_load_return"
  ``case loopSem$sh_mem_load 1 (3w : 8 word) 0
      (^s with <| locals := insert 1 (Word (0w : 8 word)) LN;
                  sh_mdomain := {3w}; ffi := ^returning_ffi |>) of
      (res,s') => (res, (case lookup 1 s'.locals of
        SOME (Word w) => w = 3w | _ => F), LENGTH s'.ffi.io_events)``

val _ = print_eval "ws_sh_mem_load_final"
  ``case loopSem$sh_mem_load 1 (3w : 8 word) 0
      (^s with <| locals := insert 1 (Word (0w : 8 word)) LN;
                  sh_mdomain := {3w}; ffi := ^final_ffi |>) of
      (res,s') => (res, (case lookup 1 s'.locals of NONE => T | _ => F))``

val _ = print_eval "ws_sh_mem_store_return"
  ``case loopSem$sh_mem_store 1 (3w : 8 word) 0
      (^s with <| locals := insert 1 (Word (7w : 8 word)) LN;
                  sh_mdomain := {3w}; ffi := ^returning_ffi |>) of
      (res,_) => res``
