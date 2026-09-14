(*
  Direct HOL-EVAL fixture for the CakeML FFI call_FFI boundary.
  Reference: cakeml/semantics/ffi/ffiScript.sml:45-79.
  The observations cover a length-preserving oracle return with event append,
  a length mismatch, an oracle-final result, and the empty ExtCall identity.
*)
load "bossLib";
load "preamble";
load "../semantics/ffi/ffiTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open ffiTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val return_oracle =
  ``(λname:ffi$ffiname. λst:unit. λconf:word8 list. λbytes:word8 list.
      ffi$Oracle_return st [5w; 6w])``;

val short_oracle =
  ``(λname:ffi$ffiname. λst:unit. λconf:word8 list. λbytes:word8 list.
      ffi$Oracle_return st [5w])``;

val final_oracle =
  ``((λname:ffi$ffiname. λst:unit. λconf:word8 list. λbytes:word8 list.
      ffi$Oracle_final ffi$FFI_diverged) :
      ffi$ffiname -> unit -> word8 list -> word8 list ->
        unit ffi$oracle_result)``;

val _ = print_eval "oracle_return"
  ``case ffi$call_FFI
      <| oracle := ^return_oracle; ffi_state := (); io_events := [] |>
      (ffi$ExtCall «foo») [1w; 2w] [3w; 4w] of
      | ffi$FFI_return st bytes =>
          (bytes, st.ffi_state, LENGTH st.io_events,
            case st.io_events of
            | [ffi$IO_event name conf pairs] => (name, conf, pairs)
            | _ => (ffi$ExtCall «bad», [], []))
      | ffi$FFI_final _ => ([], (), 0, (ffi$ExtCall «bad», [], []))``;

val _ = print_eval "length_failure"
  ``case ffi$call_FFI
      <| oracle := ^short_oracle; ffi_state := (); io_events := [] |>
      (ffi$ExtCall «foo») [1w; 2w] [3w; 4w] of
      | ffi$FFI_return _ _ => ffi$FFI_failed
      | ffi$FFI_final (ffi$Final_event _ _ _ outcome) => outcome``;

val _ = print_eval "oracle_final"
  ``case ffi$call_FFI
      <| oracle := ^final_oracle; ffi_state := (); io_events := [] |>
      (ffi$ExtCall «foo») [1w] [3w] of
      | ffi$FFI_return _ _ => ffi$FFI_failed
      | ffi$FFI_final (ffi$Final_event _ _ _ outcome) => outcome``;

val _ = print_eval "empty_extcall"
  ``case ffi$call_FFI
      <| oracle := ^final_oracle; ffi_state := (); io_events := [] |>
      (ffi$ExtCall «») [1w] [3w; 4w] of
      | ffi$FFI_return st bytes => (bytes, LENGTH st.io_events)
      | ffi$FFI_final _ => ([], 99)``;
