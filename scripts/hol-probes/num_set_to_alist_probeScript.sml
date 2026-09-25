load "preamble";
load "miscTheory";
open bossLib; open HolKernel Parse; open preamble; open miscTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val t0 = ``(LN : unit spt)``;
val t1 = ``insert 0 () ^t0``;
val t2 = ``insert 1 () ^t1``;
val t3 = ``insert 2 () ^t2``;
val t4 = ``insert 5 () ^t1``;
val t5 = ``insert 3 () ^t3``;

val _ = print_eval "toalist_ln" ``toAList ^t0``;
val _ = print_eval "toalist_zero" ``toAList ^t1``;
val _ = print_eval "toalist_two" ``toAList ^t2``;
val _ = print_eval "toalist_three" ``toAList ^t3``;
val _ = print_eval "toalist_five" ``toAList ^t4``;
val _ = print_eval "toalist_four" ``toAList ^t5``;
