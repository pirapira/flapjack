load "preamble";
load "miscTheory";
open bossLib; open HolKernel Parse; open preamble; open miscTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "lookup_ln" ``lookup 0 (LN : unit spt) = NONE``;
val _ = print_eval "insert0" ``insert 0 () (LN : unit spt) = LS ()``;
val _ = print_eval "lookup_ins0" ``lookup 0 (insert 0 () (LN : unit spt)) = SOME ()``;
val _ = print_eval "lookup_ins1_0" ``lookup 0 (insert 1 () (insert 0 () (LN : unit spt))) = SOME ()``;
val _ = print_eval "lookup_ins_other" ``lookup 5 (insert 2 () (LN : unit spt)) = NONE``;
val _ = print_eval "insert1_shape" ``insert 1 () (LN : unit spt) = BN LN (LS ())``;
val _ = print_eval "insert2_shape" ``insert 2 () (LN : unit spt) = BN (LS ()) LN``;
val _ = print_eval "wf_ins" ``wf (insert 1 () (insert 0 () (LN : unit spt))) = T``;
val _ = print_eval "isempty_ln" ``isEmpty (LN : unit spt) = T``;
val _ = print_eval "isempty_ins" ``isEmpty (insert 0 () (LN : unit spt)) = F``;
val _ = print_eval "insert_ovw" ``lookup 0 (insert 0 () (insert 0 () (LN : unit spt))) = SOME ()``;
