load "bossLib";
load "preamble";
load "mlstringTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open mlstringTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL of the `mlstring`/`char` carrier used by the CakeML backend
   FFI field of `stackLang$prog` (cakeml/compiler/backend/stackLangScript.sml:27-66)
   and by the `stack_names` program theorems.  Defined in

     cakeml/basis/pure/mlstringScript.sml:19-21
       Datatype: mlstring = implode string
     (with HOL `string = char list`; HOL `char` is the 256-element type with
      CHR : num -> char and ORD : char -> num)

   Rows check the constructor/accessor behaviour that the exact Lean carrier
   Flapjack.Compiler.Backend.MlString.MlString must match: the field is the
   character list, `explode` inverts `implode`, `strlen` counts characters, and
   the 256 character codes round-trip.  (Bead flapjack-pxn.18.5.15.3.11.2.1.)

   Provenance: generated from the Flapjack checkout with the
   coordinator-approved read-only prebuilt CakeML/HOL object directory as oracle
   input, without editing that checkout (flapjack2, which has mlstringTheory
   prebuilt at basis/pure/.hol/objs):

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=mlstring_carrier_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede; their
   basis/pure/mlstringScript.sml is byte-identical
   (sha256 f8850ef788b132f2b5e98a336dda884050618b2afcf3e1133135bd648c9ad7b1). *)

val _ = print_eval "ml_strlen"       ``strlen (strlit [CHR 65; CHR 66; CHR 67]) : num``;
val _ = print_eval "ml_ord0"         ``ORD (CHR 0) : num``;
val _ = print_eval "ml_ord255"       ``ORD (CHR 255) : num``;
val _ = print_eval "ml_chr_ord"      ``(CHR (ORD (CHR 200)) = (CHR 200))``;
val _ = print_eval "ml_explode_len"  ``LENGTH (explode (strlit [CHR 65; CHR 66])) : num``;
val _ = print_eval "ml_implode_explode"
  ``(implode (explode (strlit [CHR 65; CHR 66])) = strlit [CHR 65; CHR 66])``;
val _ = print_eval "ml_explode_implode"
  ``(explode (implode (([CHR 65; CHR 66]) : char list)) = [CHR 65; CHR 66])``;
val _ = print_eval "ml_concat_len"
  ``LENGTH (explode (concat [strlit [CHR 65]; strlit [CHR 66; CHR 67]])) : num``;