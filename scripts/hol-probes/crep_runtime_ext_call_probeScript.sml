(* Direct HOL-EVAL observations for the call_FFI boundary that the Crep
   external-call handler must respect.

   Reference:
     cakeml/semantics/ffi/ffiScript.sml: call_FFI_def

   The Crep production handler `riscv64ExtCallCallFfiHandler` dispatches an
   `ExtCall` request to the Lean counterpart `callFfi` of HOL `call_FFI`.  The
   rows below pin the three HOL outcomes on a concrete oracle:
     * the empty-name identity (no oracle call),
     * a successful oracle return whose length matches (FFI_return),
     * a successful oracle return whose length differs (FFI_final FFI_failed),
     * an oracle that diverges (FFI_final FFI_diverged).
*)
load "bossLib";
load "preamble";
load "ffiTheory";
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

(* oracle: ExtCall "f" returns one extra byte per input byte (length matches);
   ExtCall "g" returns a fixed two-byte list (length may differ); anything else
   diverges. *)
val oc =
  ``(λ (name : ffiname) (s : num) (conf : word8 list) (bytes : word8 list).
        case name of
          ExtCall «f» => Oracle_return (s + 1) (MAP (λb:word8. b) bytes)
        | ExtCall «g» => Oracle_return s [0w; 1w]
        | ExtCall «live» => Oracle_final FFI_diverged
        | _ => Oracle_final FFI_failed)
     : num oracle``;

val st = ``initial_ffi_state ^oc (0:num)``;
val conf = ``([1w; 2w; 3w] : word8 list)``;
val bytes3 = ``([10w; 20w; 30w] : word8 list)``;

val _ = print_eval "empty_name_identity"
  ``(case call_FFI ^st (ExtCall «») ^conf ^bytes3 of
      FFI_return st' bs => bs = ^bytes3
    | FFI_final _ => F)``;
val _ = print_eval "return_matching_length"
  ``(case call_FFI ^st (ExtCall «f») ^conf ^bytes3 of
      FFI_return st' bs =>
        (bs = ^bytes3) /\ (st'.ffi_state = 1) /\ (LENGTH st'.io_events = 1)
    | FFI_final _ => F)``;
val _ = print_eval "return_length_mismatch"
  ``(case call_FFI ^st (ExtCall «g») ^conf ^bytes3 of
      FFI_return _ _ => F
    | FFI_final (Final_event nm c b out) =>
        (nm = ExtCall «g») /\ (out = FFI_failed))``;
val _ = print_eval "oracle_diverged"
  ``(case call_FFI ^st (ExtCall «live») ^conf ^bytes3 of
      FFI_return _ _ => F
    | FFI_final (Final_event nm c b out) =>
        (nm = ExtCall «live») /\ (out = FFI_diverged))``;
