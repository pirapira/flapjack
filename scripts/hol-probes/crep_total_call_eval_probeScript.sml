(* Direct HOL EVAL cases for the source-code-map Call clause in crepSem. *)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;
open crepLangTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val code =
  ``alist_to_fmap
      [(«id», ([0], (Return [Var 0] : 64 crepLang$prog)))] :
      (funname, num list # 64 crepLang$prog) fmap``;
val wrongArityCode =
  ``alist_to_fmap
      [(«id», ([], (Return [Const (9w:64 word)] : 64 crepLang$prog)))] :
      (funname, num list # 64 crepLang$prog) fmap``;

fun mkState code =
  ``(<| locals := (FEMPTY |+ (0, Word (7w:64 word)) |+ (1, Word (3w:64 word)));
        globals := FEMPTY;
        code := ^code;
        memory := K (Word (0w:64 word));
        memaddrs := {};
        sh_memaddrs := {};
        clock := 5;
        be := F;
        ffi := ARB;
        base_addr := (0w:64 word);
        top_addr := (100w:64 word) |> : (64, unit) crepSem$state)``;

val s = mkState code;
val z = ``(^s with clock := 0)``;
val wrong = mkState wrongArityCode;

val _ = print_eval "call_total_return_success"
  ``case evaluate ((Call NONE «id» [Const (9w:64 word)] : 64 crepLang$prog), ^s) of
      (SOME (Return [Word v]), st) => v = (9w:64 word) /\ st.clock = 4 /\
        FLOOKUP st.locals 0 = NONE | _ => F``;
val _ = print_eval "call_total_return_destination"
  ``case evaluate ((Call (SOME ([1], NONE)) «id» [Const (9w:64 word)] : 64 crepLang$prog), ^s) of
      (NONE, st) => st.clock = 4 /\ FLOOKUP st.locals 0 = SOME (Word (7w:64 word)) /\
        FLOOKUP st.locals 1 = SOME (Word (9w:64 word)) | _ => F``;
val _ = print_eval "call_total_missing_code"
  ``case evaluate ((Call NONE «missing» [Const (9w:64 word)] : 64 crepLang$prog), ^s) of
      (SOME Error, st) => st.clock = 5 /\ FLOOKUP st.locals 0 = SOME (Word (7w:64 word)) | _ => F``;
val _ = print_eval "call_total_wrong_arity"
  ``case evaluate ((Call NONE «id» [Const (9w:64 word)] : 64 crepLang$prog), ^wrong) of
      (SOME Error, st) => st.clock = 5 /\ FLOOKUP st.locals 1 = SOME (Word (3w:64 word)) | _ => F``;
val _ = print_eval "call_total_timeout"
  ``case evaluate ((Call NONE «id» [Const (9w:64 word)] : 64 crepLang$prog), ^z) of
      (SOME TimeOut, st) => st.clock = 0 /\ FLOOKUP st.locals 0 = NONE | _ => F``;

val normalCode =
  ``alist_to_fmap
      [(«worker», ([], (Skip : 64 crepLang$prog)))] :
      (funname, num list # 64 crepLang$prog) fmap``;
val breakCode =
  ``alist_to_fmap
      [(«worker», ([], (Break 0 : 64 crepLang$prog)))] :
      (funname, num list # 64 crepLang$prog) fmap``;
val continueCode =
  ``alist_to_fmap
      [(«worker», ([], (Continue 0 : 64 crepLang$prog)))] :
      (funname, num list # 64 crepLang$prog) fmap``;
val exceptionCode =
  ``alist_to_fmap
      [(«worker», ([], (Raise (3w:64 word) : 64 crepLang$prog)))] :
      (funname, num list # 64 crepLang$prog) fmap``;
val oneReturnCode =
  ``alist_to_fmap
      [(«ret», ([], (Return [Const (9w:64 word)] : 64 crepLang$prog)))] :
      (funname, num list # 64 crepLang$prog) fmap``;

val _ = print_eval "call_total_callee_normal"
  ``case evaluate ((Call NONE «worker» [] : 64 crepLang$prog), ^(mkState normalCode)) of
      (SOME Error, st) => st.clock = 4 /\ FLOOKUP st.locals 0 = NONE | _ => F``;
val _ = print_eval "call_total_callee_break"
  ``case evaluate ((Call NONE «worker» [] : 64 crepLang$prog), ^(mkState breakCode)) of
      (SOME Error, st) => st.clock = 4 /\ FLOOKUP st.locals 0 = NONE | _ => F``;
val _ = print_eval "call_total_callee_continue"
  ``case evaluate ((Call NONE «worker» [] : 64 crepLang$prog), ^(mkState continueCode)) of
      (SOME Error, st) => st.clock = 4 /\ FLOOKUP st.locals 0 = NONE | _ => F``;
val _ = print_eval "call_total_callee_exception"
  ``case evaluate ((Call NONE «worker» [] : 64 crepLang$prog), ^(mkState exceptionCode)) of
      (SOME (Exception (3w:64 word)), st) => st.clock = 4 /\ FLOOKUP st.locals 0 = NONE | _ => F``;
val _ = print_eval "call_total_return_arity_error"
  ``case evaluate ((Call (SOME ([1;2], NONE)) «ret» [] : 64 crepLang$prog), ^(mkState oneReturnCode)) of
      (SOME Error, st) => st.clock = 4 /\ FLOOKUP st.locals 0 = NONE | _ => F``;
val _ = print_eval "call_total_duplicate_destinations"
  ``case evaluate ((Call (SOME ([1;1], NONE)) «id» [Const (9w:64 word)] : 64 crepLang$prog), ^s) of
      (SOME Error, st) => st.clock = 5 /\ FLOOKUP st.locals 0 = SOME (Word (7w:64 word)) | _ => F``;
val _ = print_eval "call_total_missing_destination"
  ``case evaluate ((Call (SOME ([9], NONE)) «id» [Const (9w:64 word)] : 64 crepLang$prog), ^s) of
      (SOME Error, st) => st.clock = 4 /\ FLOOKUP st.locals 0 = NONE | _ => F``;
