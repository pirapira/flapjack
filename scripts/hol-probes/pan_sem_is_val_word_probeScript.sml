load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "is_valword_val" ``isValWord (ValWord (7w : 8 word) : 8 panSem$v)``;
val _ = print_eval "is_valword_rstruct" ``isValWord (RStruct ([] : 8 panSem$v list))``;
val _ = print_eval "is_valword_nstruct" ``isValWord (NStruct «A» ([] : (fldname # 8 panSem$v) list))``;
val _ = print_eval "is_valword_wordlab" ``isValWord (Val (Word (7w : 8 word)) : 8 panSem$v)``;
