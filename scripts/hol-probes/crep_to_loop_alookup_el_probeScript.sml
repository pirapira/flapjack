(* Direct HOL oracle for crep_to_loopProofScript.sml `alookup_el_pair_eq_el`. *)
load "bossLib";
load "preamble";
load "listTheory";
load "mlstringTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

val aprog = ``[(«a»,([],(7:num))); («b»,([],(9:num)))] : (mlstring # num list # num) list``;

val _ = print_eval "ael_shape_0" (``(EL 0 ^aprog = («a», [], SND (SND (EL 0 ^aprog))))``);
val _ = print_eval "ael_shape_1" (``(EL 1 ^aprog = («b», [], SND (SND (EL 1 ^aprog))))``);
val _ = print_eval "ael_distinct" (``ALL_DISTINCT (MAP FST ^aprog)``);
val _ = print_eval "ael_lookup" (``ALOOKUP ^aprog «b» = SOME ([], 9)``);
val _ = print_eval "ael_result" (``(EL 1 ^aprog = («b», [], 9))``);
