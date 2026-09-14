(* Direct HOL outputs for gen_temps, rt_var, and rt_vars. *)
load "bossLib";
load "preamble";
load "crep_to_loopTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "gen_temps"
  ``crep_to_loop$gen_temps 7 3``
val _ = print_eval "rt_var_none"
  ``crep_to_loop$rt_var (FEMPTY : num |-> num) NONE 9 10``
val _ = print_eval "rt_var_hit"
  ``crep_to_loop$rt_var ((FEMPTY : num |-> num) |+ (1,5)) (SOME 1) 9 10``
val _ = print_eval "rt_var_miss"
  ``crep_to_loop$rt_var ((FEMPTY : num |-> num) |+ (1,5)) (SOME 2) 9 10``
val _ = print_eval "rt_vars_hit"
  ``crep_to_loop$rt_vars
      ((FEMPTY : num |-> num) |+ (1,5) |+ (2,6)) [1;2] 10``
val _ = print_eval "rt_vars_miss"
  ``crep_to_loop$rt_vars ((FEMPTY : num |-> num) |+ (1,5)) [1;2] 10``
