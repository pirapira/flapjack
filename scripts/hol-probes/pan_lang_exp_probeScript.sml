load "bossLib";
load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL over the `panLang$exp` datatype
   (cakeml/pancake/panLangScript.sml:53-69):

     exp = Const ('a word) | Var varkind varname | RStruct (exp list) |
       RField index exp | NStruct stcname ((fldname # exp) list) |
       NField fldname exp | Load shape exp | Load32 exp | LoadByte exp |
       Op binop (exp list) | Panop panop (exp list) | Cmp cmp exp exp |
       Shift shift exp exp | BaseAddr | TopAddr | BytesInWord

   where varname/stcname/fldname are `mlstring` (lines 23-31) and `index` is
   `num`.  The executable `Flapjack.Exp alpha` is generic over the word type and
   uses Lean `String` identifiers, so it is untagged.  The exact counterpart
   `Flapjack.Pancake.PanLang.ExpHOL width` uses `BitVec width` for `Const` and
   the faithful `MlString` carrier for identifiers.

   The rows below pin the word payload of `Const`, the name fields as
   `mlstring`, and representative constructor arities at the HOL numeral word
   type 64.

   Provenance: generated from the Flapjack checkout with the coordinator-approved
   read-only prebuilt CakeML/HOL object directory as oracle input, without
   editing that checkout.  `panLangTheory` is prebuilt in flapjack2/3/4/6:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=pan_lang_exp_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede. *)

val _ = print_eval "ex_const"
  ``(case (Const (5w : 64 word) : 64 exp) of Const w => w2n w | _ => 0)``;
val _ = print_eval "ex_var_len"
  ``(case (Var Local (strlit "xy") : 64 exp) of Var _ nm => strlen nm | _ => 0)``;
val _ = print_eval "ex_rstruct_len"
  ``(case (RStruct [Const (1w : 64 word); Const (2w : 64 word)] : 64 exp) of
       RStruct es => LENGTH es | _ => 0)``;
val _ = print_eval "ex_rfield"
  ``(case (RField 3 (Const (1w : 64 word)) : 64 exp) of
       RField i _ => i | _ => 0)``;
val _ = print_eval "ex_nstruct_len"
  ``(case (NStruct (strlit "S")
             [(strlit "f", Const (1w : 64 word));
              (strlit "g", Const (2w : 64 word))] : 64 exp) of
       NStruct _ flds => LENGTH flds | _ => 0)``;
val _ = print_eval "ex_nfield_len"
  ``(case (NField (strlit "foo") (Const (1w : 64 word)) : 64 exp) of
       NField nm _ => strlen nm | _ => 0)``;
val _ = print_eval "ex_load_shape"
  ``(case (Load One (Const (0w : 64 word)) : 64 exp) of
       Load sh _ => shape_to_str sh | _ => strlit "?")``;
val _ = print_eval "ex_load32"
  ``(case (Load32 (Const (7w : 64 word)) : 64 exp) of Load32 _ => 1 | _ => 0)``;
val _ = print_eval "ex_op_len"
  ``(case (Op Add [Const (1w : 64 word); Const (2w : 64 word)] : 64 exp) of
       Op _ es => LENGTH es | _ => 0)``;
val _ = print_eval "ex_panop_len"
  ``(case (Panop Mul [(Const (1w : 64 word))] : 64 exp) of
       Panop _ es => LENGTH es | _ => 0)``;
val _ = print_eval "ex_cmp"
  ``(case (Cmp Equal (Const (1w : 64 word)) (Const (2w : 64 word)) : 64 exp) of
       Cmp _ _ _ => 1 | _ => 0)``;
val _ = print_eval "ex_shift"
  ``(case (Shift Lsl (Const (1w : 64 word)) (Const (2w : 64 word)) : 64 exp) of
       Shift _ _ _ => 1 | _ => 0)``;
val _ = print_eval "ex_baseaddr"
  ``(case (BaseAddr : 64 exp) of BaseAddr => 1 | _ => 0)``;
val _ = print_eval "ex_topaddr"
  ``(case (TopAddr : 64 exp) of TopAddr => 1 | _ => 0)``;
val _ = print_eval "ex_bytesinword"
  ``(case (BytesInWord : 64 exp) of BytesInWord => 1 | _ => 0)``;
