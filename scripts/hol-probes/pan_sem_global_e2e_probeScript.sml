(*
  Minimal global-declaration source-execution probe for the original CakeML
  Pancake semantics.  The state contains the global initializer result and
  the parsed source's main body; the expected observation is independent of
  the Lean RISC-V execution.

  Reference: cakeml/pancake/semantics/panSemScript.sml:212 (global lookup),
  :814-830 (declaration state), and :694-736 (call evaluation).
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

val _ = print_eval "global_g_7"
  ``FST (panSem$evaluate
      (panLang$Call NONE «main» [],
       (((ARB:((8),unit) panSem$state) with clock := 20) with
         globals := FEMPTY |+ («g», panSem$Val (panSem$Word (7w:8 word)))) with
         code := FEMPTY |+
           («main», ([], panLang$Return (panLang$Var panLang$Global «g»),
                      panLang$One))))``
