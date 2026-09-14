(* Direct HOL-EVAL probes for crepLang$exps.
   Reference: cakeml/pancake/crepLangScript.sml:193-207. *)
load "bossLib";
load "preamble";
load "../crepLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "leaves"
  ``(crepLang$exps (Const (3w : 8 word)),
    crepLang$exps (Var 7),
    crepLang$exps (LoadGlob (2w : 5 word)),
    crepLang$exps BaseAddr,
    crepLang$exps TopAddr)``;
val _ = print_eval "loads"
  ``(crepLang$exps (Load (Var 1)),
    crepLang$exps (Load32 (LoadByte (Var 2))))``;
val _ = print_eval "ops"
  ``(crepLang$exps (Op Add [Const (1w : 8 word); Var 4]),
    crepLang$exps (Crepop Mul [Load (Var 2); Const (5w : 8 word)]),
    crepLang$exps (Cmp Equal (Var 6) (Const (0w : 8 word))),
    crepLang$exps (Shift Lsl (Var 8) (Const (1w : 8 word))))``;
