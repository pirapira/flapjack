(*
  Direct HOL-EVAL observations for the WordLang max_var instruction and
  return carriers.  These are the frame-sizing inputs consumed by
  word_to_stack$compile_prog; the equations are from wordLangScript.sml.
*)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_allocTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "maxvar_inst_mem"
  ``max_var (Inst (Mem Store 7 (Addr 12 (0w:64 word))):64 wordLang$prog)``
val _ = print_eval "maxvar_return"
  ``max_var (Return 7 [4;12]:64 wordLang$prog)``
