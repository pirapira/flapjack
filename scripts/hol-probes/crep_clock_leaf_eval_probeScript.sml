(* Direct Cake/HOL observations for the total Crep evaluate leaf clauses
   Skip, Break, Continue, and Tick over the exact 11-field Crep state. *)

load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val s =
  ``(<| locals := (FEMPTY |+ (0, Word (7w:64 word)));
        globals := FEMPTY;
        code := FEMPTY;
        memory := K (Word (0w:64 word));
        memaddrs := {};
        sh_memaddrs := {};
        clock := 5;
        be := F;
        ffi := ARB;
        base_addr := (0w:64 word);
        top_addr := (100w:64 word) |> : (64, unit) crepSem$state)``;
val s0 = ``^s with clock := 0``;

val _ = print_eval "skip_eval"
  ``evaluate ((Skip) : 64 crepLang$prog, ^s) = (NONE, ^s)``;
val _ = print_eval "break_eval"
  ``evaluate ((Break (1:num)) : 64 crepLang$prog, ^s) =
      (SOME (Break (1:num)), ^s)``;
val _ = print_eval "continue_eval"
  ``evaluate ((Continue (2:num)) : 64 crepLang$prog, ^s) =
      (SOME (Continue (2:num)), ^s)``;
val _ = print_eval "tick_zero_eval"
  ``evaluate ((Tick) : 64 crepLang$prog, ^s0) =
      (SOME TimeOut, empty_locals ^s0)``;
val _ = print_eval "tick_positive_eval"
  ``evaluate ((Tick) : 64 crepLang$prog, ^s) =
      (NONE, dec_clock ^s)``;
