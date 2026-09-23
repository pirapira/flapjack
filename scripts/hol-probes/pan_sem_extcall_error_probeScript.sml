(*
  Original PanSem ExtCall Error probe.

  HOL reference: cakeml/pancake/semantics/panSemScript.sml:716-729.  An
  `ExtCall` whose argument expression is not a word, or whose byte read fails,
  returns `(SOME Error, s)` with the unchanged state.  The two observed
  rejection branches are the non-word argument and the failing byte read
  (empty `memaddrs`).
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
      memory := (λa : 8 word. panSem$Word (0w:8 word));
      memaddrs := {};
      sh_memaddrs := {} |>)``

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

val _ = print_eval "ext_nonword_result"
  ``FST (panSem$evaluate (^nonword, ^baseState))``
val _ = print_eval "ext_nonword_clock"
  ``(SND (panSem$evaluate (^nonword, ^baseState))).clock``
val _ = print_eval "ext_nonword_locals"
  ``FLOOKUP (SND (panSem$evaluate (^nonword, ^baseState))).locals «x»``
val _ = print_eval "ext_read_fail_result"
  ``FST (panSem$evaluate (^readfail, ^baseState))``
val _ = print_eval "ext_read_fail_clock"
  ``(SND (panSem$evaluate (^readfail, ^baseState))).clock``
val _ = print_eval "ext_read_fail_locals"
  ``FLOOKUP (SND (panSem$evaluate (^readfail, ^baseState))).locals «x»``