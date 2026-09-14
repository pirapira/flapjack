(*
  Minimal source-execution probe for the original CakeML Pancake semantics of
  the `dec_clock` artifact fixture `fun 1 main() { tick; return 7; }`.  The
  probe evaluates the sequenced `tick` then `return` directly, so the expected
  observation (result value and decremented clock) is independent of the Lean
  RISC-V execution and of the generated artifact.

  Reference: cakeml/pancake/semantics/panSemScript.sml:615-617 (`Seq`),
  :638-643 (`Return`), :653-655 (`Tick`), and :441-443 (`dec_clock_def`).
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

val prog =
  ``panLang$Seq panLang$Tick
      (panLang$Return (panLang$Const (7w:8 word)))``;

val _ = print_eval "dec_clock_tick_return"
  ``FST (panSem$evaluate (^prog, (^s with clock := 5)))``;
val _ = print_eval "dec_clock_tick_return_clock"
  ``(SND (panSem$evaluate (^prog, (^s with clock := 5)))).clock``;
