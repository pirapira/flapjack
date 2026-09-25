load "bossLib";
load "preamble";
load "crepLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL over the `crepLang$exp` datatype
   (cakeml/pancake/crepLangScript.sml:26-37):

     exp = Const ('a word) | Var varname | Load exp | Load32 exp |
       LoadByte exp | LoadGlob (5 word) | Op binop (exp list) |
       Crepop crepop (exp list) | Cmp cmp exp exp | Shift shift exp exp |
       BaseAddr | TopAddr

   where varname is `num` and the word payloads are `'a word` (plus the fixed
   `5 word` in LoadGlob).  The executable `Flapjack.CrepExp alpha` is generic
   over the word type and is untagged; the exact counterpart
   `Flapjack.CrepExpHOL width` uses `BitVec width`.

   Rows pin the word payloads, arities, and the fixed LoadGlob width at the HOL
   numeral word type 8.

   Provenance: generated from the Flapjack checkout with the coordinator-approved
   read-only prebuilt CakeML/HOL object directory as oracle input, without
   editing that checkout:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=crep_lang_exp_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   cakeml submodule HEAD 857f0d98da8f8a3580f34423338e697809308ede. *)
load "bossLib";
load "preamble";
load "crepLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "cexp_const"
  ``(case (crepLang$Const (5w : 8 word) : 8 crepLang$exp) of
       crepLang$Const w => w2n w | _ => 0)``;
val _ = print_eval "cexp_var"
  ``(case (crepLang$Var 7 : 8 crepLang$exp) of crepLang$Var n => n | _ => 0)``;
val _ = print_eval "cexp_load"
  ``(case (crepLang$Load (crepLang$Const (1w : 8 word)) : 8 crepLang$exp) of
       crepLang$Load _ => 1 | _ => 0)``;
val _ = print_eval "cexp_load32"
  ``(case (crepLang$Load32 (crepLang$Const (1w : 8 word)) : 8 crepLang$exp) of
       crepLang$Load32 _ => 1 | _ => 0)``;
val _ = print_eval "cexp_loadbyte"
  ``(case (crepLang$LoadByte (crepLang$Const (1w : 8 word)) : 8 crepLang$exp) of
       crepLang$LoadByte _ => 1 | _ => 0)``;
val _ = print_eval "cexp_loadglob"
  ``(case (crepLang$LoadGlob (7w : 5 word) : 8 crepLang$exp) of
       crepLang$LoadGlob w => w2n w | _ => 0)``;
val _ = print_eval "cexp_op_len"
  ``(case (crepLang$Op asm$Add
            [crepLang$Const (1w : 8 word); crepLang$Const (2w : 8 word)]
          : 8 crepLang$exp) of crepLang$Op _ es => LENGTH es | _ => 0)``;
val _ = print_eval "cexp_crepop_len"
  ``(case (crepLang$Crepop crepLang$Mul [crepLang$Const (1w : 8 word)]
          : 8 crepLang$exp) of crepLang$Crepop _ es => LENGTH es | _ => 0)``;
val _ = print_eval "cexp_cmp"
  ``(case (crepLang$Cmp asm$Equal (crepLang$Const (1w : 8 word))
            (crepLang$Const (2w : 8 word)) : 8 crepLang$exp) of
       crepLang$Cmp _ _ _ => 1 | _ => 0)``;
val _ = print_eval "cexp_shift"
  ``(case (crepLang$Shift ast$Lsl (crepLang$Const (1w : 8 word))
            (crepLang$Const (2w : 8 word)) : 8 crepLang$exp) of
       crepLang$Shift _ _ _ => 1 | _ => 0)``;
val _ = print_eval "cexp_baseaddr"
  ``(case (crepLang$BaseAddr : 8 crepLang$exp) of crepLang$BaseAddr => 1 | _ => 0)``;
val _ = print_eval "cexp_topaddr"
  ``(case (crepLang$TopAddr : 8 crepLang$exp) of crepLang$TopAddr => 1 | _ => 0)``;
