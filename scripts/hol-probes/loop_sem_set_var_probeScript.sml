(*
  Direct HOL-EVAL probes for the original CakeML Pancake Loop set_var.
  Reference: cakeml/pancake/semantics/loopSemScript.sml:108-110.
  Results are observed through the original get_vars lookup boundary and are
  checked in by scripts/hol-probes/regenerate.sh.
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val s = ``(s:('a,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "set_var_new"
  ``get_vars [3] (set_var 3 (Word 5w) (^s with locals := LN))``
val _ = print_eval "set_var_overwrite"
  ``get_vars [3] (set_var 3 (Word 5w)
      (^s with locals := insert 3 (Word 1w) LN))``
val _ = print_eval "set_var_sibling"
  ``get_vars [4] (set_var 3 (Word 5w)
      (^s with locals := insert 4 (Word 7w) LN))``
val _ = print_eval "set_var_missing"
  ``get_vars [5] (set_var 3 (Word 5w) (^s with locals := LN))``
