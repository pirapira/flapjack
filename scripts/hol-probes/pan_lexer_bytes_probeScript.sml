(* pan_lexer_bytes_probe: direct HOL oracle for the original Pancake lexer's
   treatment of non-ASCII bytes (bead flapjack-pxn.18.3.5.8.7).

   HOL `char` has exactly 256 values (`CHR : num -> char`) and `string` is an
   abbreviation for `char list` (`stringScript.sml:236`), so a byte >= 128 is a
   representable `char` but is neither `isLower`/`isUpper` nor `isDigit`
   (stringScript.sml:74-95 are ASCII range tests). `pancake_lex` therefore
   cannot produce an identifier containing such a byte.

   Source: cakeml/pancake/parser/panLexerScript.sml (isAlphaNumOrWild_def:61,
   next_atom_def:225, pancake_lex_def:314) and
   cakeml/.../stringScript.sml:74-95,236.

   Provenance: read-only prebuilt oracle checkout /home/zksecurity/flapjack2/cakeml
   (cakeml submodule HEAD 857f0d98da8f8a3580f34423338e697809308ede, the same
   commit as the flap-ds2 submodule); the flap-ds2 checkout has no built HOL
   theories. Regenerate with:
     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=pan_lexer_bytes_probeScript.sml timeout 250 \
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

val _ = print_eval "plx_alpha_206" ``(isAlphaNum (CHR 206) : bool)``;
val _ = print_eval "plx_alpha_ascii" ``(isAlphaNum (#"a") : bool)``;
val _ = print_eval "plx_alpha_accent" ``(isAlphaNum (CHR 233) : bool)``;
val _ = print_eval "plx_high_first_iserror"
  ``((case pancake_lex [CHR 206; #"x"] of
        ((LexErrorT m, _) :: _) => T | (_ :: _) => F | [] => F) : bool)``;
val _ = print_eval "plx_ascii_ident_len"
  ``((case pancake_lex [#"a"; #"b"; #"c"] of
        ((IdentT s, _) :: _) => LENGTH s | (_ :: _) => 0n | [] => 0n) : num)``;
val _ = print_eval "plx_ascii_then_high"
  ``((case pancake_lex [#"a"; #"b"; CHR 206] of
        ((IdentT s, _) :: (LexErrorT m, _) :: _) => LENGTH s | _ => 0n) : num)``;
