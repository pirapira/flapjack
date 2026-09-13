(*
  Minimal ordinary-memory source-execution probe for the original CakeML
  Pancake semantics.  The loaded byte is installed in the same one-word
  memory domain used by the Lean RISC-V fixture.

  Reference: cakeml/pancake/semantics/panSemScript.sml:137-151
  (mem_load) and :247 (Load expression evaluation).
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

val memory_state =
  ``(((ARB:((8),unit) panSem$state) with clock := 20) with
      memory := (1000w =+ panSem$Word (37w:8 word))
        (λ_. panSem$Word (0w:8 word))) with
      memaddrs := {1000w}``

val _ = print_eval "memory_load_37"
  ``FST (panSem$evaluate
      (panLang$Return
        (panLang$Load panLang$One (panLang$Const (1000w:8 word))),
       ^memory_state))``
