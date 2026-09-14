(*
  Direct HOL observations for ext_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:625-642.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;
val ffi =
  ``<| oracle := (λname. λst. λconf. λbytes. ffi$Oracle_return st bytes);
      ffi_state := (); io_events := [] |>``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "ext_ffi"
  ``(ext ^s 19 ^ffi).ffi = ^ffi``;

val _ = print_eval "ext_clock"
  ``(ext ^s 19 ^ffi).clock = 19``;

val _ = print_eval "ext_locals"
  ``(ext ^s 19 ^ffi).locals = s.locals``;
