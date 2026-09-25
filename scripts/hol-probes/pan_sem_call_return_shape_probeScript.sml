(*
  Direct original CakeML oracle for Call and DecCall when a code-map entry's
  return shape disagrees with its returned value. HOL returns SOME Error and
  the callee post-state; this guards the production state-owned evaluator's
  error result and clock/local projection.

  Reference: cakeml/pancake/semantics/panSemScript.sml:657-713.
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

val baseState = ``((ARB:((8),unit) panSem$state) with
  <| clock := 5;
     locals := FEMPTY |+ (strlit "caller", ValWord (3w:8 word));
     globals := FEMPTY;
     memory := (\(_ : 8 word). Word (0w:8 word));
     memaddrs := {};
     sh_memaddrs := {};
     code := FEMPTY |+ (strlit "badret",
       ([] : (mlstring # panLang$shape) list,
        panLang$Return (panLang$Const (7w:8 word)),
        panLang$Comb [panLang$One; panLang$One])) |>)``;

(* A well-shaped code-map entry returns its value even though the Lean
   functions-list compatibility API can be supplied a conflicting, separate
   return-contract table. HOL has only the code-map `returnShape` here. *)
val goodState = ``(^baseState with code := FEMPTY |+ (strlit "goodret",
  ([] : (mlstring # panLang$shape) list,
   panLang$Return (panLang$Const (7w:8 word)), panLang$One)))``;

val _ = print_eval "call_good_return_shape_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "goodret") [], ^goodState))``;

val _ = print_eval "call_bad_return_shape_result"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "badret") [], ^baseState))``;
val _ = print_eval "call_bad_return_shape_clock"
  ``(SND (panSem$evaluate
      (panLang$Call NONE (strlit "badret") [], ^baseState))).clock``;
val _ = print_eval "call_bad_return_shape_caller_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "badret") [], ^baseState))).locals
      (strlit "caller")``;
val _ = print_eval "deccall_bad_return_shape_result"
  ``FST (panSem$evaluate
      (panLang$DecCall (strlit "dest") panLang$One (strlit "badret") []
         panLang$Skip, ^baseState))``;
val _ = print_eval "deccall_bad_return_shape_clock"
  ``(SND (panSem$evaluate
      (panLang$DecCall (strlit "dest") panLang$One (strlit "badret") []
         panLang$Skip, ^baseState))).clock``;
val _ = print_eval "deccall_bad_return_shape_caller_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$DecCall (strlit "dest") panLang$One (strlit "badret") []
         panLang$Skip, ^baseState))).locals
      (strlit "caller")``;

(* Unlike the zero-parameter call above, this distinguishes the callee's
   initial parameter bindings from its post-Return empty locals. *)
val parameterState = ``(^baseState with code :=
  FEMPTY |+ (strlit "badret_param",
    ([(strlit "x", panLang$One)] : (mlstring # panLang$shape) list,
     panLang$Return (panLang$Const (7w:8 word)),
     panLang$Comb [panLang$One; panLang$One])))``;
val _ = print_eval "call_bad_return_shape_param_local"
  ``FLOOKUP (SND (panSem$evaluate
      (panLang$Call NONE (strlit "badret_param")
         [panLang$Const (4w:8 word)], ^parameterState))).locals
      (strlit "x")``;
