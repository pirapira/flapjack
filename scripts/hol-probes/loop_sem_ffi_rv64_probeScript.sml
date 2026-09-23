(*
  64-bit RISC-V direct HOL-EVAL fixture for the Pancake loopSem evaluate_def
  ExtCall / call_FFI case.  Mirrors the three cases exercised by
  Flapjack/Test/LoopFfiParity.lean:
    * a successful ExtCall whose returned bytes are written back through
      write_bytearray while locals are preserved;
    * a terminal oracle result that becomes FinalFFI and clears the locals;
    * a missing pointer local that yields Error.
  It also prints the intermediate lookups, byte loads, and byte-array reads so a
  mismatch can be localised.  Reference: cakeml/pancake/semantics/loopSemScript.sml:427-440.
  64-bit byte_align rounds down to a multiple of 8 and get_byte uses
  address MOD 8, so the addresses below are already 8-aligned and the array
  bytes sit at indices 0 and 1 of one word.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(64,'ffi) loopSem$state)``;
val returning_ffi =
  ``<| oracle := (λname st conf bytes. ffi$Oracle_return st [0x11w; 0x22w]);
      ffi_state := (); io_events := [] |>``;
val final_ffi =
  ``<| oracle := (λname st conf bytes. ffi$Oracle_final ffi$FFI_failed);
      ffi_state := (); io_events := [] |>``;
fun base_with ffi =
  ``(^s with <|
      locals := insert 0 (Word (0w:64 word))
        (insert 1 (Word (1w:64 word))
          (insert 2 (Word (8w:64 word)) (insert 3 (Word (2w:64 word)) LN)));
      memory := (0w =+ Word (0xABw:64 word))
        ((8w =+ Word (0xEFCDw:64 word)) (K (Word (0w:64 word))));
      mdomain := {0w; 8w}; be := F; ffi := ^ffi |>)``;

fun print_eval label q =
  let
    val th0 = SIMP_CONV (srw_ss())
      [evaluate_def, eval_def, set_var_def, get_vars_def,
       call_env_def, dec_clock_def, fix_clock_def] q
    val th1 = QCONV EVAL (rconc th0)
    val th2 = QCONV (SIMP_CONV (srw_ss())
      [evaluate_def, eval_def, set_var_def, get_vars_def,
       call_env_def, dec_clock_def, fix_clock_def]) (rconc th1)
    val th = QCONV EVAL (rconc th2)
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "rv64_lookups"
  ``let st = ^(base_with returning_ffi) in
      (lookup 0 st.locals, lookup 1 st.locals, lookup 2 st.locals, lookup 3 st.locals)``

val _ = print_eval "rv64_mem_load_byte_aux"
  ``let st = ^(base_with returning_ffi) in
      (mem_load_byte_aux st.memory st.mdomain st.be 0w,
       mem_load_byte_aux st.memory st.mdomain st.be 8w,
       mem_load_byte_aux st.memory st.mdomain st.be 9w)``

val _ = print_eval "rv64_read_bytearrays"
  ``let st = ^(base_with returning_ffi) in
      (read_bytearray 0w 1 (mem_load_byte_aux st.memory st.mdomain st.be),
       read_bytearray 8w 2 (mem_load_byte_aux st.memory st.mdomain st.be))``

val _ = print_eval "rv64_extcall_returned"
  ``case loopSem$evaluate
      (loopLang$FFI (strlit "x") 0 1 2 3 (insert 0 () (insert 1 () (insert 2 () (insert 3 () LN)))),
       ^(base_with returning_ffi)) of
      (res,s') => (res, s'.memory 0w, s'.memory 8w, lookup 1 s'.locals)``

val _ = print_eval "rv64_extcall_final"
  ``case loopSem$evaluate
      (loopLang$FFI (strlit "x") 0 1 2 3 (insert 0 () (insert 1 () (insert 2 () (insert 3 () LN)))),
       ^(base_with final_ffi)) of
      (res,s') => (res, lookup 1 s'.locals)``

val _ = print_eval "rv64_extcall_missing_local"
  ``case loopSem$evaluate
      (loopLang$FFI (strlit "x") 99 1 2 3 (insert 0 () (insert 1 () (insert 2 () (insert 3 () LN)))),
       ^(base_with returning_ffi)) of
      (res,s') => (res, lookup 1 s'.locals)``

(* The four argument locals are read from the PRE-cut locals, so an empty
   cutset still calls the oracle and the result locals are cut to the cutset. *)
val _ = print_eval "rv64_extcall_precut_empty_cutset"
  ``case loopSem$evaluate
      (loopLang$FFI (strlit "x") 0 1 2 3 LN,
       ^(base_with returning_ffi)) of
      (res,s') => (res, s'.memory 8w, lookup 1 s'.locals)``

val _ = print_eval "rv64_extcall_precut_partial_cutset"
  ``case loopSem$evaluate
      (loopLang$FFI (strlit "x") 0 1 2 3 (insert 1 () LN),
       ^(base_with returning_ffi)) of
      (res,s') => (res, lookup 1 s'.locals, lookup 0 s'.locals)``

(* A live local that is absent from the pre-cut locals fails cut_state. *)
val _ = print_eval "rv64_extcall_live_absent"
  ``case loopSem$evaluate
      (loopLang$FFI (strlit "x") 0 1 2 3 (insert 7 () LN),
       ^(base_with returning_ffi)) of
      (res,s') => (res, lookup 1 s'.locals)``
