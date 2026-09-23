(*
  Minimal source-execution probe for nested propagation of the original
  CakeML Pancake semantic `Error` result.  A rejected `Dec` is nested inside
  `Seq` and `While`; the probe observes the result and clock directly, so the
  expected values are independent of the Lean evaluator:

  * `Seq` returns the `SOME Error` of its first statement unchanged (clock
    preserved);
  * `While` returns the `SOME Error` produced by its body (clock reduced by
    one iteration).

  Reference: cakeml/pancake/semantics/panSemScript.sml:653-736 (`Seq`,
  `While`).
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

val s = ``(s:(8,'ffi) panSem$state)``;

val baseState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)) |>)``;

val decMismatch = ``panLang$Dec (strlit "x") (panLang$Named (strlit "Other"))
  (panLang$Const (7w:8 word)) panLang$Skip``;

val seqProgram = ``panLang$Seq ^decMismatch panLang$Skip``;

val whileProgram = ``panLang$While (panLang$Const (1w:8 word)) ^decMismatch``;

val _ = print_eval "seq_error_result"
  ``FST (panSem$evaluate (^seqProgram, ^baseState))``;
val _ = print_eval "seq_error_clock"
  ``(SND (panSem$evaluate (^seqProgram, ^baseState))).clock``;
val _ = print_eval "seq_error_locals"
  ``FLOOKUP (SND (panSem$evaluate (^seqProgram, ^baseState))).locals (strlit "x")``;

val _ = print_eval "while_error_result"
  ``FST (panSem$evaluate (^whileProgram, ^baseState))``;
val _ = print_eval "while_error_clock"
  ``(SND (panSem$evaluate (^whileProgram, ^baseState))).clock``;
val _ = print_eval "while_error_locals"
  ``FLOOKUP (SND (panSem$evaluate (^whileProgram, ^baseState))).locals (strlit "x")``;