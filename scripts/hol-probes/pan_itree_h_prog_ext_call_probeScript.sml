(*
  Direct HOL observations for h_prog_ext_call_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:415-443.
  Zero-length arrays make read_bytearray succeed without requiring a memory
  fixture; the probe still exercises the FFI event and continuation branches.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "ext_call_event"
  ``case h_prog_ext_call (strlit "foo")
      (panLang$Const (0w:8 word)) (panLang$Const (0w:8 word))
      (panLang$Const (0w:8 word)) (panLang$Const (0w:8 word)) ^s of
      | itreeTau$Vis e k => SOME e
      | _ => NONE``;

val _ = print_eval "ext_call_empty"
  ``case h_prog_ext_call (strlit "")
      (panLang$Const (0w:8 word)) (panLang$Const (0w:8 word))
      (panLang$Const (0w:8 word)) (panLang$Const (0w:8 word)) ^s of
      | itreeTau$Ret (INR (NONE,s')) => T
      | _ => F``;

val _ = print_eval "ext_call_final_locals"
  ``case h_prog_ext_call (strlit "foo")
      (panLang$Const (0w:8 word)) (panLang$Const (0w:8 word))
      (panLang$Const (0w:8 word)) (panLang$Const (0w:8 word)) ^s of
      | itreeTau$Vis e k =>
          (case k (INL (INL FFI_failed)) of
             | itreeTau$Ret (INR (SOME (FinalFFI ev),s')) =>
                 s'.locals = FEMPTY
             | _ => F)
      | _ => F``;
