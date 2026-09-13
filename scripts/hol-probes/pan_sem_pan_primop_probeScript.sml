(*
  Probe outputs for the original CakeML Pancake panSem definition pan_primop.
  This is intentionally a HOL script rather than a second implementation.
  The checked-in output is regenerated with scripts/hol-probes/regenerate.sh.

  Reference: cakeml/pancake/semantics/panSemScript.sml:196-207 (pan_primop_def).

  The state is unneeded; pan_primop only inspects its argument list.  Words are
  fixed to 8 bits so that dimword (:'a) evaluates to 256, and results are
  printed as numeric w2n values to avoid raw word-literal printing.
*)
load "bossLib";
load "preamble";
load "../semantics/panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

val toNum = ``(\(x:8 v). case x of Val (Word (w:8 word)) => w2n w | RStruct _ => 0 | NStruct _ _ => 0)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

fun print_primop label args =
  print_eval label
    ``(case panSem$pan_primop panLang$AddCarry ^args of
        | NONE => NONE
        | SOME (RStruct vs) => SOME (MAP ^toNum vs)
        | SOME _ => NONE)``

val _ = print_primop "pan_primop_basic"
  ``[ValWord (40w:8 word); ValWord (50w:8 word); ValWord (0w:8 word)]``
val _ = print_primop "pan_primop_overflow"
  ``[ValWord (200w:8 word); ValWord (100w:8 word); ValWord (0w:8 word)]``
val _ = print_primop "pan_primop_carry_is_bit"
  ``[ValWord (5w:8 word); ValWord (7w:8 word); ValWord (2w:8 word)]``
val _ = print_primop "pan_primop_wrong_length"
  ``[ValWord (5w:8 word); ValWord (7w:8 word)]``
val _ = print_primop "pan_primop_non_word"
  ``[ValWord (5w:8 word); RStruct []; ValWord (3w:8 word)]``
