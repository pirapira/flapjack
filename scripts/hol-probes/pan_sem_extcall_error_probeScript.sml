(*
  Original PanSem ExtCall Error probe.

  HOL reference: cakeml/pancake/semantics/panSemScript.sml:716-729.  An
  `ExtCall` whose argument expression is not a word, or whose byte read fails,
  returns `(SOME Error, s)` with the unchanged state.  The byte-read failure is
  driven by an empty `memaddrs` set while `memory` still returns `Word 0w`, and
  the probe also observes representative globals, memory and FFI cells of the
  returned state.
*)
load "bossLib";
load "preamble";
load "../semantics/panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val s = ``(s:((8),unit) panSem$state)``;
val baseState =
  ``(^s with <| clock := 5;
      locals := FEMPTY |+ («x», ValWord (3w:8 word)) |+ («s», RStruct []);
      globals := FEMPTY |+ («g», ValWord (4w:8 word));
      memory := (λa : 8 word. panSem$Word (0w:8 word));
      memaddrs := {};
      sh_memaddrs := {};
      ffi := <| oracle := (λn (st:unit) b1 b2. Oracle_final FFI_failed);
                ffi_state := ();
                io_events := [] |>;
      structs := [];
      code := FEMPTY;
      eshapes := FEMPTY;
      be := F;
      base_addr := 0w;
      top_addr := 100w |>)``

val nonword =
  ``panLang$ExtCall «f»
      (panLang$Var panLang$Local «s»)
      (panLang$Const (0w:8 word))
      (panLang$Const (0w:8 word))
      (panLang$Const (0w:8 word))``

val readfail =
  ``panLang$ExtCall «f»
      (panLang$Const (0w:8 word))
      (panLang$Const (1w:8 word))
      (panLang$Const (0w:8 word))
      (panLang$Const (0w:8 word))``

val argfail =
  ``panLang$ExtCall «f»
      (panLang$Var panLang$Local «missing»)
      (panLang$Const (0w:8 word))
      (panLang$Const (0w:8 word))
      (panLang$Const (0w:8 word))``

val _ = print_eval "ext_nonword_result"
  ``FST (panSem$evaluate (^nonword, ^baseState))``
val _ = print_eval "ext_nonword_clock"
  ``(SND (panSem$evaluate (^nonword, ^baseState))).clock``
val _ = print_eval "ext_nonword_locals"
  ``FLOOKUP (SND (panSem$evaluate (^nonword, ^baseState))).locals «x»``
val _ = print_eval "ext_nonword_globals"
  ``FLOOKUP (SND (panSem$evaluate (^nonword, ^baseState))).globals «g»``
val _ = print_eval "ext_read_fail_result"
  ``FST (panSem$evaluate (^readfail, ^baseState))``
val _ = print_eval "ext_read_fail_clock"
  ``(SND (panSem$evaluate (^readfail, ^baseState))).clock``
val _ = print_eval "ext_read_fail_locals"
  ``FLOOKUP (SND (panSem$evaluate (^readfail, ^baseState))).locals «x»``
val _ = print_eval "ext_read_fail_globals"
  ``FLOOKUP (SND (panSem$evaluate (^readfail, ^baseState))).globals «g»``
val _ = print_eval "ext_read_fail_memory"
  ``(SND (panSem$evaluate (^readfail, ^baseState))).memory (0w:8 word)``
val _ = print_eval "ext_read_fail_ffi_state"
  ``(SND (panSem$evaluate (^readfail, ^baseState))).ffi.ffi_state``
val _ = print_eval "ext_read_fail_ffi_io"
  ``(SND (panSem$evaluate (^readfail, ^baseState))).ffi.io_events``

val _ = print_eval "ext_argfail_result"
  ``FST (panSem$evaluate (^argfail, ^baseState))``
val _ = print_eval "ext_argfail_clock"
  ``(SND (panSem$evaluate (^argfail, ^baseState))).clock``
val _ = print_eval "ext_argfail_locals"
  ``FLOOKUP (SND (panSem$evaluate (^argfail, ^baseState))).locals «x»``
val _ = print_eval "ext_argfail_globals"
  ``FLOOKUP (SND (panSem$evaluate (^argfail, ^baseState))).globals «g»``
val _ = print_eval "ext_argfail_memory"
  ``(SND (panSem$evaluate (^argfail, ^baseState))).memory (0w:8 word)``
val _ = print_eval "ext_argfail_ffi_io"
  ``(SND (panSem$evaluate (^argfail, ^baseState))).ffi.io_events``
val _ = print_eval "ext_argfail_structs"
  ``(SND (panSem$evaluate (^argfail, ^baseState))).structs``
val _ = print_eval "ext_argfail_code"
  ``FLOOKUP (SND (panSem$evaluate (^argfail, ^baseState))).code «f»``
val _ = print_eval "ext_argfail_eshapes"
  ``FLOOKUP (SND (panSem$evaluate (^argfail, ^baseState))).eshapes «E»``
val _ = print_eval "ext_argfail_memaddrs"
  ``(0w:8 word) IN (SND (panSem$evaluate (^argfail, ^baseState))).memaddrs``
val _ = print_eval "ext_argfail_sh_memaddrs"
  ``(0w:8 word) IN (SND (panSem$evaluate (^argfail, ^baseState))).sh_memaddrs``
val _ = print_eval "ext_argfail_be"
  ``(SND (panSem$evaluate (^argfail, ^baseState))).be``
val _ = print_eval "ext_argfail_base_addr"
  ``(SND (panSem$evaluate (^argfail, ^baseState))).base_addr``
val _ = print_eval "ext_argfail_top_addr"
  ``(SND (panSem$evaluate (^argfail, ^baseState))).top_addr``
val _ = print_eval "ext_argfail_ffi_state"
  ``(SND (panSem$evaluate (^argfail, ^baseState))).ffi.ffi_state``
val _ = print_eval "ext_argfail_done"
  ``0``
