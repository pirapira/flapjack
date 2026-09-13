(*
  Probe outputs for the original CakeML Pancake loopSem definition loop_arith.
  This is intentionally a HOL script rather than a second implementation.
  The checked-in output is regenerated with scripts/hol-probes/regenerate.sh.

  Reference: cakeml/pancake/semantics/loopSemScript.sml:118-145 (loop_arith_def).

  The state is fixed to 8-bit words so that dimword (:'a) evaluates to 256.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:(8,'ffi) loopSem$state)``;

val toNum = ``(\(l:8 word_loc). case l of Word (w:8 word) => w2n w | wordLang$Loc a b => a)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

(* LDiv: destination 1, dividend 2, divisor 3 *)
val ldivBase =
  ``(^s with locals := insert 2 (Word (7w:8 word)) (insert 3 (Word (2w:8 word)) LN))``;
val _ = print_eval "loop_arith_div"
  ``(case loop_arith ^ldivBase (LDiv 1 2 3) of NONE => NONE | SOME s' => OPTION_MAP (MAP ^toNum) (get_vars [1] s'))``
val ldivZero =
  ``(^s with locals := insert 2 (Word (7w:8 word)) (insert 3 (Word (0w:8 word)) LN))``;
val _ = print_eval "loop_arith_div_by_zero"
  ``(case loop_arith ^ldivZero (LDiv 1 2 3) of NONE => NONE | SOME s' => OPTION_MAP (MAP ^toNum) (get_vars [1] s'))``
val ldivNonWord =
  ``(^s with locals := insert 2 (wordLang$Loc 9 0) (insert 3 (Word (2w:8 word)) LN))``;
val _ = print_eval "loop_arith_div_non_word"
  ``(case loop_arith ^ldivNonWord (LDiv 1 2 3) of NONE => NONE | SOME s' => OPTION_MAP (MAP ^toNum) (get_vars [1] s'))``

(* LLongMul: destinations 1 (high) and 2 (low), sources 3, 4 *)
val lmulBase =
  ``(^s with locals := insert 3 (Word (20w:8 word)) (insert 4 (Word (20w:8 word)) LN))``;
val _ = print_eval "loop_arith_longmul"
  ``(case loop_arith ^lmulBase (LLongMul 1 2 3 4) of NONE => NONE | SOME s' => OPTION_MAP (MAP ^toNum) (get_vars [1;2] s'))``
val lmulNonWord =
  ``(^s with locals := insert 3 (wordLang$Loc 9 0) (insert 4 (Word (20w:8 word)) LN))``;
val _ = print_eval "loop_arith_longmul_non_word"
  ``(case loop_arith ^lmulNonWord (LLongMul 1 2 3 4) of NONE => NONE | SOME s' => OPTION_MAP (MAP ^toNum) (get_vars [1;2] s'))``

(* LLongDiv: destinations 1 (quotient) and 2 (remainder), sources 3,4 (numerator), 5 (divisor) *)
val ldivLongBase =
  ``(^s with locals := insert 3 (Word (1w:8 word)) (insert 4 (Word (3w:8 word)) (insert 5 (Word (2w:8 word)) LN)))``;
val _ = print_eval "loop_arith_longdiv"
  ``(case loop_arith ^ldivLongBase (LLongDiv 1 2 3 4 5) of NONE => NONE | SOME s' => OPTION_MAP (MAP ^toNum) (get_vars [1;2] s'))``
val ldivLongZero =
  ``(^s with locals := insert 3 (Word (1w:8 word)) (insert 4 (Word (3w:8 word)) (insert 5 (Word (0w:8 word)) LN)))``;
val _ = print_eval "loop_arith_longdiv_by_zero"
  ``(case loop_arith ^ldivLongZero (LLongDiv 1 2 3 4 5) of NONE => NONE | SOME s' => OPTION_MAP (MAP ^toNum) (get_vars [1;2] s'))``
val ldivLongOverflow =
  ``(^s with locals := insert 3 (Word (1w:8 word)) (insert 4 (Word (0w:8 word)) (insert 5 (Word (1w:8 word)) LN)))``;
val _ = print_eval "loop_arith_longdiv_overflow"
  ``(case loop_arith ^ldivLongOverflow (LLongDiv 1 2 3 4 5) of NONE => NONE | SOME s' => OPTION_MAP (MAP ^toNum) (get_vars [1;2] s'))``
