(*
  Minimal source-execution probe for the original CakeML Pancake semantics.
  This is the authoritative expected result for the checked-in Lean
  source-to-RISC-V execution fixture, not a second Lean oracle.

  Reference: cakeml/pancake/semantics/panSemScript.sml:638-643
  (Return evaluation) and :787-809 (bounded observational execution).
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

val _ = print_eval "return_41"
  ``FST (panSem$evaluate
      (panLang$Return (panLang$Const (41w:8 word)),
       (ARB:((8),unit) panSem$state)))``

val _ = print_eval "return_mul_42"
  ``FST (panSem$evaluate
      (panLang$Return
        (panLang$Panop panLang$Mul
          [panLang$Const (6w:8 word); panLang$Const (7w:8 word)]),
       (ARB:((8),unit) panSem$state)))``

val _ = print_eval "return_if_13"
  ``FST (panSem$evaluate
      (panLang$If (panLang$Const (1w:8 word))
        (panLang$Return (panLang$Const (13w:8 word)))
        (panLang$Return (panLang$Const (99w:8 word))),
       (ARB:((8),unit) panSem$state)))``

val _ = print_eval "call_code_map_7"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "id") [panLang$Const (7w:8 word)],
       ((ARB:((8),unit) panSem$state) with
          <| code := FEMPTY |+ (strlit "id",
               ([ (strlit "x", panLang$One) ],
                panLang$Return (panLang$Var panLang$Local (strlit "x")), panLang$One));
             clock := 10 |>)))``

val _ = print_eval "call_assign_local_7"
  ``(FST (panSem$evaluate
      (panLang$Call (SOME (SOME (panLang$Local, strlit "answer"), NONE))
        (strlit "id") [panLang$Const (7w:8 word)],
       ((ARB:((8),unit) panSem$state) with
          <| code := FEMPTY |+ (strlit "id",
               ([ (strlit "x", panLang$One) ],
                panLang$Return (panLang$Var panLang$Local (strlit "x")), panLang$One));
             locals := FEMPTY |+ (strlit "answer", ValWord (3w:8 word));
             clock := 10 |>))),
     FLOOKUP (SND (panSem$evaluate
      (panLang$Call (SOME (SOME (panLang$Local, strlit "answer"), NONE))
        (strlit "id") [panLang$Const (7w:8 word)],
       ((ARB:((8),unit) panSem$state) with
          <| code := FEMPTY |+ (strlit "id",
               ([ (strlit "x", panLang$One) ],
                panLang$Return (panLang$Var panLang$Local (strlit "x")), panLang$One));
             locals := FEMPTY |+ (strlit "answer", ValWord (3w:8 word));
             clock := 10 |>)))).locals (strlit "answer"))``

val _ = print_eval "call_raises_exception_7"
  ``FST (panSem$evaluate
      (panLang$Call NONE (strlit "raiseE") [],
       ((ARB:((8),unit) panSem$state) with
          <| eshapes := FEMPTY |+ (strlit "E", panLang$One);
             code := FEMPTY |+ (strlit "raiseE",
               ([], panLang$Raise (strlit "E")
                   (panLang$Const (7w:8 word)), panLang$One));
             clock := 10 |>)))``

val _ = print_eval "call_handles_exception_7"
  ``FST (panSem$evaluate
      (panLang$Call
        (SOME (NONE, SOME (strlit "E", strlit "caught",
          panLang$Return (panLang$Var panLang$Local (strlit "caught")))))
        (strlit "raiseE") [],
       ((ARB:((8),unit) panSem$state) with
          <| locals := FEMPTY |+ (strlit "caught", ValWord (0w:8 word));
             eshapes := FEMPTY |+ (strlit "E", panLang$One);
             code := FEMPTY |+ (strlit "raiseE",
               ([], panLang$Raise (strlit "E")
                   (panLang$Const (7w:8 word)), panLang$One));
             clock := 10 |>)))``

val _ = print_eval "recursive_call_code_map_7"
  ``FST (panSem$evaluate
      (panLang$Call NONE «f» [],
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («f», ([],
             panLang$DecCall «nested» panLang$One «g» []
               (panLang$Return (panLang$Var panLang$Local «nested»)),
             panLang$One)) |+
           («g», ([], panLang$Return (panLang$Const (7w:8 word)), panLang$One)))))``

val _ = print_eval "deccall_code_map_7"
  ``FST (panSem$evaluate
      (panLang$DecCall «answer» panLang$One «id»
        [panLang$Const (7w:8 word)]
        (panLang$Return (panLang$Var panLang$Local «answer»)),
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («id», ([(«x», panLang$One)],
             panLang$Return (panLang$Var panLang$Local «x»), panLang$One)))))``

val _ = print_eval "call_struct_argument_7_8"
  ``FST (panSem$evaluate
      (panLang$Call NONE «pair»
        [panLang$RStruct [panLang$Const (7w:8 word);
          panLang$Const (8w:8 word)]],
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («pair», ([(«p», panLang$Comb [panLang$One; panLang$One])],
             panLang$Return (panLang$Var panLang$Local «p»),
             panLang$Comb [panLang$One; panLang$One])))))``

val _ = print_eval "call_zero_clock_timeout"
  ``FST (panSem$evaluate
      (panLang$Call NONE «callee» [],
       (((ARB:((8),unit) panSem$state) with clock := 0) with
         code := FEMPTY |+
           («callee», ([], panLang$Skip, panLang$One)))))``

val _ = print_eval "call_zero_arg_const_7"
  ``FST (panSem$evaluate
      (panLang$Call NONE «constant» [],
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («constant», ([],
             panLang$Return (panLang$Const (7w:8 word)), panLang$One)))))``

val _ = print_eval "recursive_call_timeout"
  ``FST (panSem$evaluate
      (panLang$Call NONE «loop» [],
       (((ARB:((8),unit) panSem$state) with clock := 2) with
         code := FEMPTY |+
           («loop», ([], panLang$Call NONE «loop» [], panLang$One)))))``

val _ = print_eval "recursive_deccall_timeout"
  ``FST (panSem$evaluate
      (panLang$DecCall «answer» panLang$One «loop» [] panLang$Skip,
       (((ARB:((8),unit) panSem$state) with clock := 2) with
         code := FEMPTY |+
           («loop», ([], panLang$DecCall «nested» panLang$One «loop» []
             panLang$Skip, panLang$One)))))``
