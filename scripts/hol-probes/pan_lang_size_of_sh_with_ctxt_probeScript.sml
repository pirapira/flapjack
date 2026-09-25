load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val ctxt = ``[(«A» : stcname, (<| fields := ([] : (fldname # shape) list); size := 5n |>) : struct_info);
              («B» : stcname, (<| fields := ([] : (fldname # shape) list); size := 3n |>) : struct_info)]``;
val ctxt' = ctxt;

val _ = print_eval "sswc_one" ``size_of_sh_with_ctxt ^ctxt' (One : shape)``;
val _ = print_eval "sswc_named_hit" ``size_of_sh_with_ctxt ^ctxt' (Named «A» : shape)``;
val _ = print_eval "sswc_named_miss" ``size_of_sh_with_ctxt ^ctxt' (Named «Z» : shape)``;
val _ = print_eval "sswc_comb" ``size_of_sh_with_ctxt ^ctxt' (Comb [One; Named «A»; Named «B»] : shape)``;
val _ = print_eval "sswc_comb_miss" ``size_of_sh_with_ctxt ^ctxt' (Comb [One; Named «Z»] : shape)``;
