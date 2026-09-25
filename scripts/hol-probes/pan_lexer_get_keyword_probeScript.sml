(* pan_lexer_get_keyword_probe: direct original-HOL oracle coverage for
   `get_keyword` (bead flapjack-pxn.18.3.5.8.7.2).

   The coordinator's 371454bef head notice recorded that the parser
   ordered-table refactor still lacked direct original-HOL coverage for every
   `get_keyword` table entry and fallback.  This probe pins the original
   function for all 33 table entries (including the deliberate `@top` ->
   `BaseK` duplicate) plus the three fallbacks: the empty string
   (`LexErrorT`), an `@`-prefixed name (`ForeignIdent`), and a plain
   identifier (`IdentT`).

   Source: cakeml/pancake/parser/panLexerScript.sml:115-155.

   Regenerate with:
     CAKEML=/home/zksecurity/pancake-lean/cakeml \
       HOL_PROBE_ONLY=pan_lexer_get_keyword_probeScript.sml \
       bash scripts/hol-probes/regenerate.sh *)

load "bossLib";
load "preamble";
load "panLexerTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLexerTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

val _ = print_eval "gk_skip" ``get_keyword "skip"``;
val _ = print_eval "gk_st" ``get_keyword "st"``;
val _ = print_eval "gk_stw" ``get_keyword "stw"``;
val _ = print_eval "gk_st8" ``get_keyword "st8"``;
val _ = print_eval "gk_st16" ``get_keyword "st16"``;
val _ = print_eval "gk_st32" ``get_keyword "st32"``;
val _ = print_eval "gk_if" ``get_keyword "if"``;
val _ = print_eval "gk_else" ``get_keyword "else"``;
val _ = print_eval "gk_while" ``get_keyword "while"``;
val _ = print_eval "gk_break" ``get_keyword "break"``;
val _ = print_eval "gk_continue" ``get_keyword "continue"``;
val _ = print_eval "gk_throw" ``get_keyword "throw"``;
val _ = print_eval "gk_return" ``get_keyword "return"``;
val _ = print_eval "gk_tick" ``get_keyword "tick"``;
val _ = print_eval "gk_var" ``get_keyword "var"``;
val _ = print_eval "gk_in" ``get_keyword "in"``;
val _ = print_eval "gk_try" ``get_keyword "try"``;
val _ = print_eval "gk_catch" ``get_keyword "catch"``;
val _ = print_eval "gk_lds" ``get_keyword "lds"``;
val _ = print_eval "gk_ldw" ``get_keyword "ldw"``;
val _ = print_eval "gk_ld8" ``get_keyword "ld8"``;
val _ = print_eval "gk_ld16" ``get_keyword "ld16"``;
val _ = print_eval "gk_ld32" ``get_keyword "ld32"``;
val _ = print_eval "gk_at_base" ``get_keyword "@base"``;
val _ = print_eval "gk_at_top" ``get_keyword "@top"``;
val _ = print_eval "gk_at_biw" ``get_keyword "@biw"``;
val _ = print_eval "gk_true" ``get_keyword "true"``;
val _ = print_eval "gk_false" ``get_keyword "false"``;
val _ = print_eval "gk_fun" ``get_keyword "fun"``;
val _ = print_eval "gk_export" ``get_keyword "export"``;
val _ = print_eval "gk_inline" ``get_keyword "inline"``;
val _ = print_eval "gk_exception" ``get_keyword "exception"``;
val _ = print_eval "gk_struct" ``get_keyword "struct"``;
val _ = print_eval "gk_empty" ``get_keyword ""``;
val _ = print_eval "gk_foreign" ``get_keyword "@ffi"``;
val _ = print_eval "gk_ident" ``get_keyword "abc"``;
val _ = print_eval "gk_at_sign" ``get_keyword "@"``;
val _ = print_eval "gk_done" ``0``;
