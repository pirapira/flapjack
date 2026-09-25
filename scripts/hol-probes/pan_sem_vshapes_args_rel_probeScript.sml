(* Direct HOL-EVAL probes for CakeML Pancake panSem
   vshapes_args_rel_imp_eq_len_MAP (panSemScript.sml:740): the exact
   LIST_REL shape relation on (varname # shape) lists and value lists, with
   both the length and MAP SND/MAP shape_of conclusions. *)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "vra_one"
  ``LIST_REL (\vshape arg. SND vshape = shape_of arg)
      [("x", One)] [ValWord (3w : 64 word)]``
val _ = print_eval "vra_two"
  ``LIST_REL (\vshape arg. SND vshape = shape_of arg)
      [("x", One); ("y", One)]
      [ValWord (3w : 64 word); ValWord (4w : 64 word)]``
val _ = print_eval "vra_bad"
  ``LIST_REL (\vshape arg. SND vshape = shape_of arg)
      [("x", One)] [ValWord (3w : 64 word); ValWord (4w : 64 word)]``
val _ = print_eval "vra_len_one"
  ``(LENGTH [("x", One)] = LENGTH [ValWord (3w : 64 word)])``
val _ = print_eval "vra_map_two"
  ``(MAP SND [("x", One); ("y", One)] =
     MAP shape_of [ValWord (3w : 64 word); ValWord (4w : 64 word)])``
