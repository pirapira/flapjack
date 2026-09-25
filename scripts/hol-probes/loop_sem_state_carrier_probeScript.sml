(* Direct HOL oracle: exact loopSem state field shapes.

   We build a concrete `(8,'ffi) loopSem$state` and evaluate the projections
   that the Lean `LoopSemState` carrier mirrors (num_map locals, total memory,
   set-valued domain, clock, num_map code, be). *)

load "preamble";
load "loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val s = ``(s : (8,'ffi) loopSem$state)``;

val s1 = ``(^s with <|
  locals := sptree$insert 0 (Word (7w:8 word)) sptree$LN;
  memory := (\(_ : 8 word). Word (0w:8 word));
  mdomain := ({} : 8 word set);
  clock := 5;
  code := sptree$LN;
  be := F |>)``;

val _ = print_eval "locals_0" ``sptree$lookup 0 ^s1.locals``;
val _ = print_eval "locals_1" ``sptree$lookup 1 ^s1.locals``;
val _ = print_eval "memory_3" ``^s1.memory (3w:8 word)``;
val _ = print_eval "mdomain_3" ``(3w:8 word) IN ^s1.mdomain``;
val _ = print_eval "clock_5" ``^s1.clock``;
val _ = print_eval "code_empty" ``sptree$lookup 0 ^s1.code``;
val _ = print_eval "be_false" ``^s1.be``;
val _ = print_eval "base_self" ``^s1.base_addr = ^s.base_addr``;