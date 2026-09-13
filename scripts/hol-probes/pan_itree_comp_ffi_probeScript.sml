(*)
  Direct source probes for comp_ffi_def
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:1574-1602.
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
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

fun print_div label q =
  let
    val th = SIMP_CONV (srw_ss()) [div_Ret, div_Tau] q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val fs =
  ``(((λ(name:ffi$ffiname). λst. λconf. λbytes. ffi$Oracle_return st bytes), ()):
      unit pan_itreeSem$fst)``;

val _ = print_eval "ret" ``(comp_ffi ^fs
  (Ret (INL (INL ffi$FFI_failed)):
    (unit) pan_itreeSem$ptree))``;

val _ = print_eval "tau" ``(comp_ffi ^fs
  (Tau (Ret (INL (INL ffi$FFI_failed))):
    (unit) pan_itreeSem$ptree))``;

val _ = print_eval "return" ``(comp_ffi ^fs
  (Vis (ffi$ExtCall «foo», [], [1w:8 word])
    (λr. Ret (INL (INL ffi$FFI_failed))):
    (unit) pan_itreeSem$ptree))``;

val _ = print_div "div_ret" ``(div ^fs
  (Ret (INL (INL ffi$FFI_failed)):
    (unit) pan_itreeSem$ptree))``;

val _ = print_div "div_tau" ``(div ^fs
  (Tau (Ret (INL (INL ffi$FFI_failed))):
    (unit) pan_itreeSem$ptree))``;
