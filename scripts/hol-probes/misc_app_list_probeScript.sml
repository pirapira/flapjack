load "preamble";
load "miscTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open miscTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "append_aux_list" ``append_aux (List [1;2]) [3] : num list``;
val _ = print_eval "append_aux_append" ``append_aux (Append (List [1;2]) (List [3])) [] : num list``;
val _ = print_eval "append_list" ``append (List [1;2;3]) : num list``;
val _ = print_eval "append_append" ``append (Append (List [1]) (Append (List [2]) (List [3]))) : num list``;
val _ = print_eval "append_nil" ``append (Nil : num app_list) : num list``;
val _ = print_eval "append_aux_suffix" ``append_aux (Append (List [1]) (List [2])) [9] : num list``;