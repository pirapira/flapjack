load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val s = ``(s : (8,'ffi) panSem$state)``;
val s0 = ``(^s with <| locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)); clock := 5 |>)``;

val _ = print_eval "el_lookup" ``FLOOKUP (empty_locals ^s0).locals (strlit "x")``;
val _ = print_eval "el_clock" ``(empty_locals ^s0).clock``;
val _ = print_eval "el_globals" ``(((empty_locals ^s0).globals) = ((^s0).globals))``;