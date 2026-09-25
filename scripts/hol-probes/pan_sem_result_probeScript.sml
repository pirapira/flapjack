load "preamble";;
load "panSemTheory";;
open bossLib;;
open HolKernel Parse;;
open preamble;;
open panSemTheory;;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "res_error" ``(Error : 8 panSem$result)``;
val _ = print_eval "res_timeout" ``(TimeOut : 8 panSem$result)``;
val _ = print_eval "res_break" ``(Break : 8 panSem$result)``;
val _ = print_eval "res_continue" ``(Continue : 8 panSem$result)``;
val _ = print_eval "res_return" ``(Return (ValWord (7w:8 word)) : 8 panSem$result)``;
val _ = print_eval "res_exception" ``(Exception «E» (ValWord (7w:8 word)) : 8 panSem$result)``;
val _ = print_eval "res_finalffi" ``(FinalFFI (Final_event (ExtCall «E») [] [] FFI_failed) : 8 panSem$result)``;
val _ = print_eval "res_distinct" ``(TimeOut <> (Break : 8 panSem$result))``;