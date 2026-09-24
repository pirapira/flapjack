(* Direct Cake/HOL observations for the total Crep Assign evaluate_def clause. *)

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

val _ = print_eval "assign_overwrite_eval"
  ``case evaluate ((Assign 0 (Const (9w:64 word))) : 64 crepLang$prog, ^s) of
      (NONE, st) => FLOOKUP st.locals 0 = SOME (Word (9w:64 word)) /\
        FLOOKUP st.locals 1 = NONE
    | _ => F``;
val _ = print_eval "assign_missing_destination_eval"
  ``evaluate ((Assign 1 (Const (9w:64 word))) : 64 crepLang$prog, ^s) =
      (SOME Error, ^s)``;
val _ = print_eval "assign_expression_error_eval"
  ``evaluate ((Assign 0 (Var 9)) : 64 crepLang$prog, ^s) =
      (SOME Error, ^s)``;
