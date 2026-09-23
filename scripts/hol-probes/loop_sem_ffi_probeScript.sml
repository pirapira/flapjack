(*
  Direct HOL-EVAL fixture for the Pancake loopSem evaluate_def FFI case.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:427-440.
  The observations cover a successful ExtCall whose returned bytes are written
  back with write_bytearray, a terminal oracle result that becomes FinalFFI and
  clears the locals, and a malformed local lookup that yields Error.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(8,'ffi) loopSem$state)``;
val returning_ffi =
  ``<| oracle := (λname st conf bytes. ffi$Oracle_return st [0x11w; 0x22w]);
      ffi_state := (); io_events := [] |>``;
val final_ffi =
  ``<| oracle := (λname st conf bytes. ffi$Oracle_final ffi$FFI_failed);
      ffi_state := (); io_events := [] |>``;
fun base_with ffi =
  ``(^s with <|
      locals := insert 1 (Word (1w:8 word))
        (insert 2 (Word 3w) (insert 3 (Word 2w) (insert 4 (Word 5w) LN)));
      memory := (3w =+ Word (0xABw:8 word))
        ((5w =+ Word (0xCDw:8 word))
          ((6w =+ Word (0xEFw:8 word)) (K (Word (0w:8 word)))));
      mdomain := {3w; 5w; 6w}; be := F; ffi := ^ffi |>)``;

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

val _ = print_eval "extcall_returned"
  ``case loopSem$evaluate
      (loopLang$FFI (strlit "x") 2 1 4 3 (insert 1 () (insert 2 () (insert 3 () (insert 4 () LN)))), ^(base_with returning_ffi)) of
      (res,s') => (res, s'.memory 5w, s'.memory 6w, lookup 1 s'.locals)``
val _ = print_eval "extcall_final"
  ``case loopSem$evaluate
      (loopLang$FFI (strlit "x") 2 1 4 3 (insert 1 () (insert 2 () (insert 3 () (insert 4 () LN)))), ^(base_with final_ffi)) of
      (res,s') => (res, lookup 1 s'.locals)``
val _ = print_eval "extcall_missing_local"
  ``case loopSem$evaluate
      (loopLang$FFI (strlit "x") 9 1 4 3 (insert 1 () (insert 2 () (insert 3 () (insert 4 () LN)))), ^(base_with returning_ffi)) of
      (res,s') => (res, lookup 1 s'.locals)``
