(*
  Minimal source-execution probe for the original CakeML Pancake `DecCall`
  terminal-result handling.  The probe observes the raw result directly, so the
  expected value is independent of the Lean evaluator:

  * a callee whose body falls through (`Skip`) evaluates to `NONE`, which the
    call path rejects with `SOME Error`;
  * a callee whose body is `Break` is rejected with `SOME Error`;
  * a callee whose body is `Continue` is rejected with `SOME Error`;
  * a call naming an unknown function is rejected with `SOME Error`.

  Reference: cakeml/pancake/semantics/panSemScript.sml:657-713.
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

val probeCode = ``FEMPTY |+
  (strlit "skipf",
    ([] : (mlstring # panLang$shape) list, panLang$Skip, panLang$One)) |+
  (strlit "breakf",
    ([] : (mlstring # panLang$shape) list, panLang$Break, panLang$One)) |+
  (strlit "contf",
    ([] : (mlstring # panLang$shape) list, panLang$Continue, panLang$One)) |+
  (strlit "retf",
    ([] : (mlstring # panLang$shape) list,
     panLang$Return (panLang$Const (7w:8 word)), panLang$One))``;

val baseState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {};
  sh_memaddrs := {};
  code := ^probeCode |>)``;

val _ = print_eval "call_terminal_skip_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "skipf") []
        panLang$Skip, ^baseState))``;
val _ = print_eval "call_terminal_skip_clock"
  ``(SND (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "skipf") []
        panLang$Skip, ^baseState))).clock``;
val _ = print_eval "call_terminal_skip_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "skipf") []
        panLang$Skip, ^baseState))).locals (strlit "x")``;
val _ = print_eval "call_terminal_break_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "breakf") []
        panLang$Skip, ^baseState))``;
val _ = print_eval "call_terminal_continue_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "contf") []
        panLang$Skip, ^baseState))``;
val _ = print_eval "call_terminal_return_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "retf") []
        panLang$Skip, ^baseState))``;
val _ = print_eval "call_terminal_missing_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "g") []
        panLang$Skip, ^baseState))``;
val paramState = ``(^baseState with code := ^probeCode |+
  (strlit "skipp",
    ([(strlit "p", panLang$One)] : (mlstring # panLang$shape) list, panLang$Skip, panLang$One)) |+
  (strlit "breakp",
    ([(strlit "p", panLang$One)] : (mlstring # panLang$shape) list, panLang$Break, panLang$One)) |+
  (strlit "contp",
    ([(strlit "p", panLang$One)] : (mlstring # panLang$shape) list, panLang$Continue, panLang$One)))``;

val _ = print_eval "call_terminal_skip_param_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "skipp")
        [panLang$Const (9w:8 word)] panLang$Skip, ^paramState))``;
val _ = print_eval "call_terminal_skip_param_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "skipp")
        [panLang$Const (9w:8 word)] panLang$Skip, ^paramState))).locals (strlit "p")``;
val _ = print_eval "call_terminal_break_param_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "breakp")
        [panLang$Const (9w:8 word)] panLang$Skip, ^paramState))``;
val _ = print_eval "call_terminal_break_param_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "breakp")
        [panLang$Const (9w:8 word)] panLang$Skip, ^paramState))).locals (strlit "p")``;
val _ = print_eval "call_terminal_continue_param_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "contp")
        [panLang$Const (9w:8 word)] panLang$Skip, ^paramState))``;
val _ = print_eval "call_terminal_continue_param_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$DecCall (strlit "r") panLang$One (strlit "contp")
        [panLang$Const (9w:8 word)] panLang$Skip, ^paramState))).locals (strlit "p")``;
