load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "so_valword"
  ``shape_of (ValWord (7w : 8 word) : 8 panSem$v)``;
val _ = print_eval "so_rstruct"
  ``shape_of (RStruct [ValWord (1w : 8 word); ValWord (2w : 8 word)] : 8 panSem$v)``;
val _ = print_eval "so_nstruct"
  ``shape_of (NStruct «A» ([] : (fldname # 8 panSem$v) list) : 8 panSem$v)``;
val _ = print_eval "so_nested"
  ``shape_of (RStruct [RStruct [ValWord (3w : 8 word)]] : 8 panSem$v)``;
val _ = print_eval "so_wordlab"
  ``shape_of (Val (Word (9w : 8 word)) : 8 panSem$v)``;