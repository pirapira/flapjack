load "bossLib";
load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL over the `panLang$shape` datatype
   (cakeml/pancake/panLangScript.sml:35-39):

     shape = One | Comb (shape list) | Named stcname

   where `stcname = mlstring` (lines 23-24) and
   `mlstring = implode string` (string = char list, char the 256-element type,
   cakeml/basis/pure/mlstringScript.sml:19-21).

   The executable `Flapjack.Shape` (Flapjack/Pancake/PanLang.lean) uses Lean
   `String` for the name field, so its `@[hol ... "shape"]` tag is not exact.
   The exact counterpart `Flapjack.Pancake.PanLang.ShapeHOL` types the `named`
   field by the faithful `MlString` carrier
   (Flapjack/Basis/Pure/MlString.lean).  The rows below pin the name field as
   an mlstring by evaluating `shape_to_str` (panLangScript.sml:170-178), whose
   `Named nm` clause returns `nm` unchanged, plus the constructor equality and
   arity.

   Provenance: generated from the Flapjack checkout with the coordinator-approved
   read-only prebuilt CakeML/HOL object directory as oracle input, without
   editing that checkout.  `panLangTheory` is prebuilt in flapjack2/3/4/6:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=pan_lang_shape_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede. *)

val _ = print_eval "shp_one_str" ``(shape_to_str One : mlstring)``;
val _ = print_eval "shp_named_str"
  ``(shape_to_str (Named (strlit "Foo")) : mlstring)``;
val _ = print_eval "shp_comb_str"
  ``(shape_to_str (Comb [One; Named (strlit "Bar")]) : mlstring)``;
val _ = print_eval "shp_named_explode"
  ``(explode (shape_to_str (Named (strlit "Foo"))) : char list)``;
val _ = print_eval "shp_named_eq"
  ``((Named (strlit "Foo") : shape) = Named (strlit "Foo"))``;
val _ = print_eval "shp_named_ne"
  ``((Named (strlit "Foo") : shape) = Named (strlit "Bar"))``;
val _ = print_eval "shp_comb_len"
  ``(LENGTH ([One; Named (strlit "Bar")] : shape list) : num)``;
