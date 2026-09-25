load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

(* An oracle that returns a same-length zero byte list, so `call_FFI` takes the
   FFI_return branch for any configuration. *)
val okOracle = ``(\(_ : ffiname) (st : unit) (conf : word8 list) (bytes : word8 list).
    Oracle_return st (REPLICATE (LENGTH bytes) (0w : word8))) : unit oracle``;
val finalOracle = ``(\(_ : ffiname) (st : unit) (conf : word8 list) (bytes : word8 list).
    Oracle_final FFI_failed) : unit oracle``;

val okFfi = ``(<| oracle := ^okOracle; ffi_state := (); io_events := [] |>) : unit ffi_state``;
val finalFfi = ``(<| oracle := ^finalOracle; ffi_state := (); io_events := [] |>) : unit ffi_state``;

val s = ``(s : (64,unit) panSem$state)``;

val base = ``(^s : (64,unit) panSem$state) with
    <| locals := FEMPTY; sh_memaddrs := {(0w:64 word)}; ffi := ^okFfi |>``;
val missBase = ``(^s : (64,unit) panSem$state) with
    <| locals := FEMPTY; sh_memaddrs := {(1w:64 word)}; ffi := ^okFfi |>``;
val alignBase = ``(^s : (64,unit) panSem$state) with
    <| locals := FEMPTY; sh_memaddrs := {(8w:64 word)}; ffi := ^okFfi |>``;
val finalBase = ``(^s : (64,unit) panSem$state) with
    <| locals := FEMPTY; sh_memaddrs := {(0w:64 word)}; ffi := ^finalFfi |>``;

val _ = print_eval "l_load_hit_local"
  ``case sh_mem_load Local «x» (0w:64 word) 0 ^base of
      | (NONE, s') => FLOOKUP s'.locals «x»
      | _ => NONE``;
val _ = print_eval "l_load_hit_events"
  ``case sh_mem_load Local «x» (0w:64 word) 0 ^base of
      | (NONE, s') => LENGTH s'.ffi.io_events
      | _ => 0``;
val _ = print_eval "l_load_miss"
  ``FST (sh_mem_load Local «x» (0w:64 word) 0 ^missBase)``;
val _ = print_eval "l_load_aligned"
  ``case sh_mem_load Local «x» (8w:64 word) 1 ^alignBase of
      | (NONE, s') => FLOOKUP s'.locals «x»
      | _ => NONE``;
val _ = print_eval "l_load_final_locals"
  ``case sh_mem_load Local «x» (0w:64 word) 0 ^finalBase of
      | (_, s') => FLOOKUP s'.locals «x»``;
val _ = print_eval "l_store_hit_events"
  ``case sh_mem_store (7w:64 word) (0w:64 word) 0 ^base of
      | (NONE, s') => LENGTH s'.ffi.io_events
      | _ => 0``;
val _ = print_eval "l_store_miss"
  ``FST (sh_mem_store (7w:64 word) (0w:64 word) 0 ^missBase)``;
val _ = print_eval "l_store_final_unchanged"
  ``case sh_mem_store (7w:64 word) (0w:64 word) 0 ^finalBase of
      | (SOME (FinalFFI (Final_event _ _ _ oc)), s') => (LENGTH s'.ffi.io_events, oc)
      | _ => (0, FFI_diverged)``;

print "done\n";