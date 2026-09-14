(*
  Direct HOL observations for trace_prefix0_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:1674-1688.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;


fun print_eval label q =
  let
    val th = SIMP_CONV (srw_ss()) [trace_prefix0_def, Once LUNFOLD] q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val fs =
  ``(((λ(name:ffi$ffiname). λst. λconf. λbytes.
          ffi$Oracle_return st bytes), ()): unit pan_itreeSem$fst)``;

val fs_short =
  ``(((λ(name:ffi$ffiname). λst. λconf. λbytes.
          ffi$Oracle_return st []), ()): unit pan_itreeSem$fst)``;

val fs_final =
  ``(((λ(name:ffi$ffiname). λst. λconf. λbytes.
          ffi$Oracle_final ffi$FFI_failed), ()): unit pan_itreeSem$fst)``;

val _ = print_eval "ret" ``trace_prefix0 ^fs
  (Ret ():
    (ffi$ffi_outcome + word8 list, pan_itreeSem$ev, unit) itree)``;

val _ = print_eval "tau_vis" ``trace_prefix0 ^fs
  (Tau (Vis (ffi$ExtCall «foo», [], [1w:8 word])
    (λr. Ret ())):
    (ffi$ffi_outcome + word8 list, pan_itreeSem$ev, unit) itree)``;

val _ = print_eval "length_failure" ``trace_prefix0 ^fs_short
  (Vis (ffi$ExtCall «foo», [], [1w:8 word])
    (λr. Ret ()):
    (ffi$ffi_outcome + word8 list, pan_itreeSem$ev, unit) itree)``;

val _ = print_eval "final" ``trace_prefix0 ^fs_final
  (Vis (ffi$ExtCall «foo», [], [1w:8 word])
    (λr. Ret ()):
    (ffi$ffi_outcome + word8 list, pan_itreeSem$ev, unit) itree)``;
