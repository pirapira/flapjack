load "bossLib";
load "preamble";
load "panPropsTheory";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;
open panPropsTheory panLangTheory;

val _ = print "pan_props_list_rel_probe\n";

fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

val sh = ``[panLang$One; panLang$One] : panLang$shape list``;
val ns = ``[0; 1] : num list``;
val args = ``[panSem$Val (panSem$Word (3w:64 word)); panSem$Val (panSem$Word (5w:64 word))] : 64 panSem$v list``;

val _ = print_eval "len0"
  ``LENGTH (EL 0 (with_shape ^sh ^ns)) = LENGTH (flatten (EL 0 ^args))``;

val _ = print_eval "len1"
  ``LENGTH (EL 1 (with_shape ^sh ^ns)) = LENGTH (flatten (EL 1 ^args))``;

val _ = print_eval "size_ok"
  ``size_of_shape (Comb ^sh) = LENGTH (FLAT (MAP flatten ^args))``;

val _ = print_eval "wf_ok"
  ``EVERY is_wf_shape_v_nil ^args``;