(*
  Source-execution probe for `Return`/`Raise` when the payload expression reads
  the source memory.  The probe observes the raw result directly, so the
  expected values are independent of the Lean evaluator:

  * `Return e` whose expression reads an address outside `memaddrs` fails to
    evaluate and yields `SOME Error` with the unchanged state (clock and locals
    preserved);
  * `Return e` whose expression reads a present word cell yields
    `SOME (Return v)` with cleared locals;
  * `Raise eid e` whose expression reads an address outside `memaddrs` yields
    `SOME Error` with the unchanged state;
  * `Raise eid e` whose payload shape does not match the declared shape yields
    `SOME Error` with the unchanged state;
  * a well-matched `Raise eid e` whose expression reads a present word cell
    yields `SOME (Exception eid v)` with cleared locals.

  Reference: cakeml/pancake/semantics/panSemScript.sml:633-650.
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
  memory := (\(a : 8 word).
    if a = (8w:8 word) then Word (0x77w:8 word) else Word (0w:8 word));
  memaddrs := {(8w:8 word)};
  sh_memaddrs := {};
  structs := [];
  eshapes := FEMPTY |>)``;

val raiseState = ``(^baseState with
  eshapes := FEMPTY |+ (strlit "E", panLang$One))``;

val raiseBadShapeState = ``(^baseState with
  eshapes := FEMPTY |+ (strlit "E", panLang$Named (strlit "Other")))``;

val _ = print_eval "ret_mem_fail_result"
  ``FST (panSem$evaluate
      (panLang$Return (panLang$Load panLang$One (panLang$Const (11w:8 word))),
        ^baseState))``;
val _ = print_eval "ret_mem_fail_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Return (panLang$Load panLang$One (panLang$Const (11w:8 word))),
        ^baseState))).locals (strlit "x")``;
val _ = print_eval "ret_mem_fail_clock"
  ``(SND (panSem$evaluate
      (panLang$Return (panLang$Load panLang$One (panLang$Const (11w:8 word))),
        ^baseState))).clock``;
val _ = print_eval "ret_mem_ok_result"
  ``FST (panSem$evaluate
      (panLang$Return (panLang$Load panLang$One (panLang$Const (8w:8 word))),
        ^baseState))``;
val _ = print_eval "ret_mem_ok_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Return (panLang$Load panLang$One (panLang$Const (8w:8 word))),
        ^baseState))).locals (strlit "x")``;

val _ = print_eval "raise_mem_fail_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "E")
        (panLang$Load panLang$One (panLang$Const (11w:8 word))), ^raiseState))``;
val _ = print_eval "raise_mem_fail_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Raise (strlit "E")
        (panLang$Load panLang$One (panLang$Const (11w:8 word))), ^raiseState))).locals
      (strlit "x")``;
val _ = print_eval "raise_mem_badshape_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "E")
        (panLang$Load panLang$One (panLang$Const (8w:8 word))), ^raiseBadShapeState))``;
val _ = print_eval "raise_mem_badshape_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Raise (strlit "E")
        (panLang$Load panLang$One (panLang$Const (8w:8 word))), ^raiseBadShapeState))).locals
      (strlit "x")``;
val _ = print_eval "raise_mem_ok_result"
  ``FST (panSem$evaluate
      (panLang$Raise (strlit "E")
        (panLang$Load panLang$One (panLang$Const (8w:8 word))), ^raiseState))``;
val _ = print_eval "raise_mem_ok_locals"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Raise (strlit "E")
        (panLang$Load panLang$One (panLang$Const (8w:8 word))), ^raiseState))).locals
      (strlit "x")``;
