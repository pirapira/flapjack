(* Direct HOL-EVAL probes for CakeML Pancake Loop get_vars / get_var_imm
   properties (loopSemScript.sml get_vars_def and loopPropsScript.sml
   get_var_imm_add_clk_eq / get_vars_local_clock_upd_eq / get_vars_clock_upd_eq). *)
load "bossLib";
load "preamble";
load "loopPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopPropsTheory;
open loopSemTheory;

val s = ``(s:(8,'ffi) loopSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val two = ``(insert 1 (Word (5w:8 word)) (insert 2 (Word (9w:8 word)) LN) : 8 word_loc sptree$num_map)``;
val one = ``(insert 1 (Word (5w:8 word)) LN : 8 word_loc sptree$num_map)``;

val _ = print_eval "get_vars_two"
  ``get_vars [1;2] (^s with locals := ^two)``
val _ = print_eval "get_vars_miss"
  ``get_vars [1;3] (^s with locals := ^one)``
val _ = print_eval "get_vars_empty"
  ``get_vars [] (^s with locals := ^one)``
val _ = print_eval "get_vars_clock_upd_eq"
  ``get_vars [1] (^s with <| locals := ^two; clock := 7 |>) =
    get_vars [1] (^s with locals := ^two)``
val _ = print_eval "get_vars_local_clock_upd_eq"
  ``get_vars [1;2] (^s with <| locals := ^two; clock := 7 |>) =
    get_vars [1;2] (^s with locals := ^two)``
val _ = print_eval "get_var_imm_add_clk_eq"
  ``get_var_imm (Imm (5w:8 word)) (^s with clock := 7) =
    get_var_imm (Imm (5w:8 word)) ^s``
