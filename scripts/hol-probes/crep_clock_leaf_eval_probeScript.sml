(* Direct Cake/HOL observations for total Crep evaluate clock leaves and the
   recursive If clause over the exact 11-field Crep state. *)

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
val _ = print_eval "if_true_eval"
  ``evaluate ((If (Const (5w:64 word)) (Break 3) Skip) : 64 crepLang$prog, ^s) =
      (SOME (Break 3), ^s)``;
val _ = print_eval "if_false_eval"
  ``evaluate ((If (Const (0w:64 word)) (Break 3) (Continue 4)) : 64 crepLang$prog, ^s) =
      (SOME (Continue 4), ^s)``;
val _ = print_eval "if_error_eval"
  ``evaluate ((If (Var 9) Skip (Break 5)) : 64 crepLang$prog, ^s) =
      (SOME Error, ^s)``;
val _ = print_eval "if_nested_eval"
  ``evaluate ((If (Const (1w:64 word))
      (If (Const (0w:64 word)) Skip (Break 6)) (Continue 4)) : 64 crepLang$prog, ^s) =
      (SOME (Break 6), ^s)``;
val _ = print_eval "seq_skip_break_eval"
  ``evaluate ((Seq Skip (Break 7)) : 64 crepLang$prog, ^s) =
      (SOME (Break 7), ^s)``;
val _ = print_eval "seq_break_stops_eval"
  ``evaluate ((Seq (Break 8) Tick) : 64 crepLang$prog, ^s) =
      (SOME (Break 8), ^s)``;
val _ = print_eval "seq_tick_skip_eval"
  ``evaluate ((Seq Tick Skip) : 64 crepLang$prog, ^s) =
      (NONE, dec_clock ^s)``;
val _ = print_eval "seq_tick_zero_eval"
  ``evaluate ((Seq Tick Skip) : 64 crepLang$prog, ^s0) =
      (SOME TimeOut, empty_locals ^s0)``;
val _ = print_eval "seq_fix_clock_upper_clamp_eval"
  ``fix_clock ^s (NONE, ^s with clock := 7) = (NONE, ^s)``;
val _ = print_eval "return_word_eval"
  ``evaluate ((Return [Const (9w:64 word)]) : 64 crepLang$prog, ^s) =
      (SOME (Return [Word (9w:64 word)]), empty_locals ^s)``;
val _ = print_eval "return_empty_eval"
  ``evaluate ((Return []) : 64 crepLang$prog, ^s) =
      (SOME (Return []), empty_locals ^s)``;
val _ = print_eval "return_missing_eval"
  ``evaluate ((Return [Var 9]) : 64 crepLang$prog, ^s) =
      (SOME Error, ^s)``;
