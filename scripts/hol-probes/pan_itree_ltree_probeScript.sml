(*
  Direct HOL observations for ltree_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:1537-1567.
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
    val th = SIMP_CONV (srw_ss())
      [ltree_def, Once itreeTauTheory.itree_iter_thm,
       itreeTauTheory.itree_bind_thm, Once ltree_def] q
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

val _ = print_eval "ret" ``ltree ^fs
  (Ret (INL (INL ffi$FFI_failed)): (unit) pan_itreeSem$ptree)``;

val _ = print_eval "tau" ``ltree ^fs
  (Tau (Ret (INL (INL ffi$FFI_failed))):
    (unit) pan_itreeSem$ptree)``;

val _ = print_eval "return" ``ltree ^fs
  (Vis (ffi$ExtCall «foo», [], [1w:8 word])
    (λr. Ret (INL (INL ffi$FFI_failed))):
    (unit) pan_itreeSem$ptree)``;

val _ = print_eval "length_failure" ``ltree ^fs_short
  (Vis (ffi$ExtCall «foo», [], [1w:8 word])
    (λr. Ret (INL (INL ffi$FFI_failed))):
    (unit) pan_itreeSem$ptree)``;

val _ = print_eval "final" ``ltree ^fs_final
  (Vis (ffi$ExtCall «foo», [], [1w:8 word])
    (λr. Ret (INL (INL ffi$FFI_failed))):
    (unit) pan_itreeSem$ptree)``;
