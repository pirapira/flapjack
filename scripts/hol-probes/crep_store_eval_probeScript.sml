(* Direct Cake/HOL observations for the total Crep Store evaluate_def clause. *)

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
        memaddrs := {10w:64 word};
        sh_memaddrs := {};
        clock := 5;
        be := F;
        ffi := ARB;
        base_addr := (0w:64 word);
        top_addr := (100w:64 word) |> : (64, unit) crepSem$state)``;

val _ = print_eval "store_success"
  ``case evaluate ((Store (Const (10w:64 word)) (Const (9w:64 word))) :
      64 crepLang$prog, ^s) of
      (NONE, st) => st.memory (10w:64 word) = Word (9w:64 word) /\
        st.memory (11w:64 word) = Word (0w:64 word)
    | _ => F``;
val _ = print_eval "store_address_error"
  ``evaluate ((Store (Var 9) (Const (9w:64 word))) : 64 crepLang$prog, ^s) =
      (SOME Error, ^s)``;
val _ = print_eval "store_value_error"
  ``evaluate ((Store (Const (10w:64 word)) (Var 9)) : 64 crepLang$prog, ^s) =
      (SOME Error, ^s)``;
val _ = print_eval "store_domain_error"
  ``evaluate ((Store (Const (11w:64 word)) (Const (9w:64 word))) :
      64 crepLang$prog, ^s) = (SOME Error, ^s)``;
