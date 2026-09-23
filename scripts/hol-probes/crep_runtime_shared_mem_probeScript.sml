(*
  Direct HOL-EVAL fixture for the Pancake shared-memory FFI case.
  Reference: cakeml/pancake/semantics/panSemScript.sml:510-548
  (`sh_mem_load_def` / `sh_mem_store_def`), the HOL original that the Crep
  `crepRuntimeSharedMem` MappedRead/MappedWrite dispatch mirrors.

  The observations cover a successful mapped read (the returned bytes are
  decoded with `word_of_bytes` into the destination local and the ffi trace
  records the `SharedMem MappedRead` IO event), an out-of-domain read (Error),
  a terminal oracle result (FinalFFI with cleared locals), a successful mapped
  write (ffi trace records `SharedMem MappedWrite`), and an out-of-domain
  write (Error).
*)
load "bossLib";
load "preamble";
load "../semantics/panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val s = ``(s:(8,'ffi) panSem$state)``;
val returning_ffi =
  ``<| oracle := (λname st conf bytes. ffi$Oracle_return st (MAP (λb. (0x42w:word8)) bytes));
      ffi_state := (); io_events := [] |>``;
val final_ffi =
  ``<| oracle := (λname st conf bytes. ffi$Oracle_final ffi$FFI_failed);
      ffi_state := (); io_events := [] |>``;
fun base_with ffi =
  ``(^s with <|
      locals := (FEMPTY : mlstring |-> 8 panSem$v);
      globals := (FEMPTY : mlstring |-> 8 panSem$v);
      memory := (K (Word (0w:8 word)));
      memaddrs := {8w};
      sh_memaddrs := {8w};
      be := F; ffi := ^ffi |>)``;

fun print_eval label q =
  let
    val th0 = SIMP_CONV (srw_ss())
      [sh_mem_load_def, sh_mem_store_def, set_kvar_def, empty_locals_def] q
    val th1 = QCONV EVAL (rconc th0)
  in
    print (label ^ "=");
    print_term (rconc th1);
    print "\n"
  end

val _ = print_eval "load_returned"
  ``case panSem$sh_mem_load Local «v» (8w:8 word) 0 ^(base_with returning_ffi) of
      (res,s') => (res, FLOOKUP s'.locals «v», LENGTH s'.ffi.io_events)``
val _ = print_eval "load_out_of_domain"
  ``case panSem$sh_mem_load Local «v» (16w:8 word) 0 ^(base_with returning_ffi) of
      (res,s') => (res, FLOOKUP s'.locals «v», LENGTH s'.ffi.io_events)``
val _ = print_eval "load_final"
  ``case panSem$sh_mem_load Local «v» (8w:8 word) 0 ^(base_with final_ffi) of
      (res,s') => (res, FLOOKUP s'.locals «v»)``
val _ = print_eval "store_returned"
  ``case panSem$sh_mem_store (0xABw:8 word) (8w:8 word) 0 ^(base_with returning_ffi) of
      (res,s') => (res, LENGTH s'.ffi.io_events)``
val _ = print_eval "store_out_of_domain"
  ``case panSem$sh_mem_store (0xABw:8 word) (16w:8 word) 0 ^(base_with returning_ffi) of
      (res,s') => (res, LENGTH s'.ffi.io_events)``
