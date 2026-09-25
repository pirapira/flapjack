(* Direct HOL oracle for `panLexer$get_keyword` (panLexerScript.sml:115-153).

   Bead flapjack-pxn.18.3.5.8.7.1.1: the executable Lean lexer replaced the
   original if-chain with the ordered `keywordTable` (Flapjack/Parser/Lexer.lean).
   These rows pin the original HOL output for every table entry plus the
   empty / `@`-foreign / ordinary-identifier fallbacks.

   Oracle provenance: read-only prebuilt checkout /home/zksecurity/flapjack2/cakeml
   (cakeml HEAD 857f0d98da8f8a3580f34423338e697809308ede). Regenerate with:
     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=pan_lexer_keyword_probeScript.sml timeout 250 \
       scripts/hol-probes/regenerate.sh </dev/null *)

load "bossLib";
load "preamble";
load "panLexerTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLexerTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

val _ = print_eval "kw_skip" ``((get_keyword "skip" = KeywordT SkipK) : bool)``;
val _ = print_eval "kw_st" ``((get_keyword "st" = KeywordT StK) : bool)``;
val _ = print_eval "kw_stw" ``((get_keyword "stw" = KeywordT StwK) : bool)``;
val _ = print_eval "kw_st8" ``((get_keyword "st8" = KeywordT St8K) : bool)``;
val _ = print_eval "kw_st16" ``((get_keyword "st16" = KeywordT St16K) : bool)``;
val _ = print_eval "kw_st32" ``((get_keyword "st32" = KeywordT St32K) : bool)``;
val _ = print_eval "kw_if" ``((get_keyword "if" = KeywordT IfK) : bool)``;
val _ = print_eval "kw_else" ``((get_keyword "else" = KeywordT ElseK) : bool)``;
val _ = print_eval "kw_while" ``((get_keyword "while" = KeywordT WhileK) : bool)``;
val _ = print_eval "kw_break" ``((get_keyword "break" = KeywordT BrK) : bool)``;
val _ = print_eval "kw_continue" ``((get_keyword "continue" = KeywordT ContK) : bool)``;
val _ = print_eval "kw_throw" ``((get_keyword "throw" = KeywordT ThrowK) : bool)``;
val _ = print_eval "kw_return" ``((get_keyword "return" = KeywordT RetK) : bool)``;
val _ = print_eval "kw_tick" ``((get_keyword "tick" = KeywordT TicK) : bool)``;
val _ = print_eval "kw_var" ``((get_keyword "var" = KeywordT VarK) : bool)``;
val _ = print_eval "kw_in" ``((get_keyword "in" = KeywordT InK) : bool)``;
val _ = print_eval "kw_try" ``((get_keyword "try" = KeywordT TryK) : bool)``;
val _ = print_eval "kw_catch" ``((get_keyword "catch" = KeywordT CatchK) : bool)``;
val _ = print_eval "kw_lds" ``((get_keyword "lds" = KeywordT LdsK) : bool)``;
val _ = print_eval "kw_ldw" ``((get_keyword "ldw" = KeywordT LdwK) : bool)``;
val _ = print_eval "kw_ld8" ``((get_keyword "ld8" = KeywordT Ld8K) : bool)``;
val _ = print_eval "kw_ld16" ``((get_keyword "ld16" = KeywordT Ld16K) : bool)``;
val _ = print_eval "kw_ld32" ``((get_keyword "ld32" = KeywordT Ld32K) : bool)``;
val _ = print_eval "kw_atbase" ``((get_keyword "@base" = KeywordT BaseK) : bool)``;
val _ = print_eval "kw_attop" ``((get_keyword "@top" = KeywordT BaseK) : bool)``;
val _ = print_eval "kw_atbiw" ``((get_keyword "@biw" = KeywordT BiwK) : bool)``;
val _ = print_eval "kw_true" ``((get_keyword "true" = KeywordT TrueK) : bool)``;
val _ = print_eval "kw_false" ``((get_keyword "false" = KeywordT FalseK) : bool)``;
val _ = print_eval "kw_fun" ``((get_keyword "fun" = KeywordT FunK) : bool)``;
val _ = print_eval "kw_export" ``((get_keyword "export" = KeywordT ExportK) : bool)``;
val _ = print_eval "kw_inline" ``((get_keyword "inline" = KeywordT InlineK) : bool)``;
val _ = print_eval "kw_exception" ``((get_keyword "exception" = KeywordT ExceptionK) : bool)``;
val _ = print_eval "kw_struct" ``((get_keyword "struct" = KeywordT NamedK) : bool)``;
val _ = print_eval "kw_empty" ``((case get_keyword "" of LexErrorT m => T | _ => F) : bool)``;
val _ = print_eval "kw_foreign" ``((get_keyword "@ffi" = ForeignIdent "ffi") : bool)``;
val _ = print_eval "kw_ordinary" ``((get_keyword "abc" = IdentT "abc") : bool)``;
val _ = print_eval "kw_at_only" ``((case get_keyword "@" of IdentT s => T | _ => F) : bool)``;