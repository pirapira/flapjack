(*
  Direct source-evaluation oracle for the statement constructors added to the
  measure-driven total PanSem fragment. It records Assign success/Error,
  Return success/Error, Raise success/Error, and these clauses under If/Seq.
  Reference: cakeml/pancake/semantics/panSemScript.sml:566-630.
*)
load "bossLib";
load "preamble";
load "../semantics/panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val s = ``(s:(8,'ffi) panSem$state)``;
val baseState = ``(^s with <| clock := 5;
  locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word));
  globals := FEMPTY;
  eshapes := FEMPTY |+ (strlit "E", One);
  memory := (\(_ : 8 word). Word (0w:8 word));
  memaddrs := {};
  sh_memaddrs := {} |>)``;
val oversizedState = ``(^baseState with eshapes := FEMPTY |+
  (strlit "E", Comb (REPLICATE 33 One)))``;

val assignOk = ``panLang$Assign Local (strlit "x") (panLang$Const (9w:8 word))``;
val assignBad = ``panLang$Assign Local (strlit "y") (panLang$Const (9w:8 word))``;
val returnOk = ``panLang$Return (panLang$Const (7w:8 word))``;
val raiseOk = ``panLang$Raise (strlit "E") (panLang$Const (4w:8 word))``;
val oversized = ``panLang$RStruct
  (REPLICATE 33 (panLang$Const (1w:8 word)))``;

val _ = print_eval "total_assign_ok_result"
  ``FST (panSem$evaluate (^assignOk, ^baseState))``;
val _ = print_eval "total_assign_ok_local"
  ``FLOOKUP (SND (panSem$evaluate (^assignOk, ^baseState))).locals (strlit "x")``;
val _ = print_eval "total_assign_bad_result"
  ``FST (panSem$evaluate (^assignBad, ^baseState))``;
val _ = print_eval "total_assign_bad_local"
  ``FLOOKUP (SND (panSem$evaluate (^assignBad, ^baseState))).locals (strlit "x")``;
val _ = print_eval "total_return_ok_result"
  ``FST (panSem$evaluate (^returnOk, ^baseState))``;
val _ = print_eval "total_return_ok_local"
  ``FLOOKUP (SND (panSem$evaluate (^returnOk, ^baseState))).locals (strlit "x")``;
val _ = print_eval "total_return_bad_result"
  ``FST (panSem$evaluate
      (panLang$Return (panLang$Var Local (strlit "missing")), ^baseState))``;
val _ = print_eval "total_return_bad_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Return (panLang$Var Local (strlit "missing")), ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "total_return_oversize_result"
  ``FST (panSem$evaluate (panLang$Return ^oversized, ^baseState))``;
val _ = print_eval "total_return_oversize_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Return ^oversized, ^baseState))).locals (strlit "x")``;
val _ = print_eval "total_raise_ok_result"
  ``FST (panSem$evaluate (^raiseOk, ^baseState))``;
val _ = print_eval "total_raise_ok_local"
  ``FLOOKUP (SND (panSem$evaluate (^raiseOk, ^baseState))).locals (strlit "x")``;
val _ = print_eval "total_raise_bad_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "E")
        (panLang$Var Local (strlit "missing")), ^baseState))``;
val _ = print_eval "total_raise_bad_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Raise (strlit "E")
        (panLang$Var Local (strlit "missing")), ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "total_raise_shape_mismatch_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "E") (panLang$RStruct []), ^baseState))``;
val _ = print_eval "total_raise_shape_mismatch_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Raise (strlit "E") (panLang$RStruct []), ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "total_raise_missing_shape_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "Missing") (panLang$Const (4w:8 word)), ^baseState))``;
val _ = print_eval "total_raise_oversize_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "E") ^oversized, ^oversizedState))``;
val _ = print_eval "total_raise_oversize_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Raise (strlit "E") ^oversized, ^oversizedState))).locals
      (strlit "x")``;
val _ = print_eval "total_if_assign_true_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word)) ^assignOk panLang$Skip, ^baseState))``;
val _ = print_eval "total_if_assign_true_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word)) ^assignOk panLang$Skip, ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "total_if_assign_false_result"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Const (0w:8 word)) ^assignOk panLang$Skip, ^baseState))``;
val _ = print_eval "total_if_assign_false_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$If (panLang$Const (0w:8 word)) ^assignOk panLang$Skip, ^baseState))).locals
      (strlit "x")``;
val _ = print_eval "total_seq_assign_return_result"
  ``FST (panSem$evaluate (panLang$Seq ^assignOk ^returnOk, ^baseState))``;
val _ = print_eval "total_seq_assign_return_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Seq ^assignOk ^returnOk, ^baseState))).locals (strlit "x")``;
val _ = print_eval "total_seq_raise_stop_result"
  ``FST (panSem$evaluate
      (panLang$Seq ^raiseOk ^assignBad, ^baseState))``;
val _ = print_eval "total_seq_raise_stop_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Seq ^raiseOk ^assignBad, ^baseState))).locals (strlit "x")``;
