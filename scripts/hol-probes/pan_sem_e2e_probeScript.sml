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

val _ = print_eval "call_code_map_clock_9"
  ``(FST (panSem$evaluate
      (panLang$Call NONE (strlit "id") [panLang$Const (7w:8 word)],
       ((ARB:((8),unit) panSem$state) with
          <| code := FEMPTY |+ (strlit "id",
               ([ (strlit "x", panLang$One) ],
                panLang$Return (panLang$Var panLang$Local (strlit "x")), panLang$One));
             clock := 10 |>))),
     (SND (panSem$evaluate
      (panLang$Call NONE (strlit "id") [panLang$Const (7w:8 word)],
       ((ARB:((8),unit) panSem$state) with
          <| code := FEMPTY |+ (strlit "id",
               ([ (strlit "x", panLang$One) ],
                panLang$Return (panLang$Var panLang$Local (strlit "x")), panLang$One));
             clock := 10 |>)))).clock)``

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

val bad_destination_call_state =
  ``((ARB:((8),unit) panSem$state) with <|
      code := FEMPTY |+ (strlit "id", ([(strlit "x", panLang$One)],
        panLang$Return (panLang$Var panLang$Local (strlit "x")), panLang$One));
      locals := FEMPTY |+ (strlit "answer",
        RStruct [ValWord (0w:8 word); ValWord (0w:8 word)]);
      clock := 10 |>)``

val bad_destination_call_program =
  ``panLang$Call (SOME (SOME (panLang$Local, strlit "answer"), NONE))
      (strlit "id") [panLang$Const (7w:8 word)]``

val _ = print_eval "call_bad_destination_shape"
  ``case panSem$evaluate (^bad_destination_call_program,
      ^bad_destination_call_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals (strlit "answer"))``

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

val _ = print_eval "call_handles_struct_exception_7_8"
  ``FST (panSem$evaluate
      (panLang$Call
        (SOME (NONE, SOME (strlit "E", strlit "caught",
          panLang$Return (panLang$Var panLang$Local (strlit "caught")))))
        (strlit "raisePair") [],
       ((ARB:((8),unit) panSem$state) with
          <| locals := FEMPTY |+ (strlit "caught",
               RStruct [ValWord (0w:8 word); ValWord (0w:8 word)]);
             eshapes := FEMPTY |+ (strlit "E", panLang$Comb [panLang$One; panLang$One]);
             code := FEMPTY |+ (strlit "raisePair",
               ([], panLang$Raise (strlit "E")
                   (panLang$RStruct [panLang$Const (7w:8 word);
                     panLang$Const (8w:8 word)]), panLang$One));
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

val _ = print_eval "recursive_call_code_map_clock_8"
  ``(FST (panSem$evaluate
      (panLang$Call NONE «f» [],
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («f», ([],
             panLang$DecCall «nested» panLang$One «g» []
               (panLang$Return (panLang$Var panLang$Local «nested»)),
             panLang$One)) |+
           («g», ([], panLang$Return (panLang$Const (7w:8 word)), panLang$One))))),
     (SND (panSem$evaluate
      (panLang$Call NONE «f» [],
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («f», ([],
             panLang$DecCall «nested» panLang$One «g» []
               (panLang$Return (panLang$Var panLang$Local «nested»)),
             panLang$One)) |+
           («g», ([], panLang$Return (panLang$Const (7w:8 word)), panLang$One)))))).clock)``

val _ = print_eval "deccall_code_map_7"
  ``FST (panSem$evaluate
      (panLang$DecCall «answer» panLang$One «id»
        [panLang$Const (7w:8 word)]
        (panLang$Return (panLang$Var panLang$Local «answer»)),
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («id», ([(«x», panLang$One)],
             panLang$Return (panLang$Var panLang$Local «x»), panLang$One)))))``

val _ = print_eval "deccall_code_map_clock_9"
  ``(FST (panSem$evaluate
      (panLang$DecCall «answer» panLang$One «id»
        [panLang$Const (7w:8 word)]
        (panLang$Return (panLang$Var panLang$Local «answer»)),
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («id», ([(«x», panLang$One)],
             panLang$Return (panLang$Var panLang$Local «x»), panLang$One))))),
     (SND (panSem$evaluate
      (panLang$DecCall «answer» panLang$One «id»
        [panLang$Const (7w:8 word)]
        (panLang$Return (panLang$Var panLang$Local «answer»)),
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («id», ([(«x», panLang$One)],
             panLang$Return (panLang$Var panLang$Local «x»), panLang$One)))))).clock)``

val deccall_existing_local_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («answer», ValWord (3w:8 word));
      code := FEMPTY |+ («id», ([(«x», panLang$One)],
        panLang$Return (panLang$Var panLang$Local «x»), panLang$One));
      clock := 10 |>)``;

val _ = print_eval "deccall_restores_existing_local"
  ``case panSem$evaluate
      (panLang$DecCall «answer» panLang$One «id» [panLang$Const (7w:8 word)]
        (panLang$Return (panLang$Var panLang$Local «answer»)),
       ^deccall_existing_local_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «answer»)``

val _ = print_eval "deccall_tick_restores_existing_local"
  ``case panSem$evaluate
      (panLang$DecCall «answer» panLang$One «id» [panLang$Const (7w:8 word)]
        panLang$Tick,
       ^deccall_existing_local_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «answer»)``

val _ = print_eval "nested_deccall_code_map_7"
  ``FST (panSem$evaluate
      (panLang$DecCall «answer» panLang$One «f» []
        (panLang$Return (panLang$Var panLang$Local «answer»)),
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («f», ([],
             panLang$DecCall «nested» panLang$One «g» []
               (panLang$Return (panLang$Var panLang$Local «nested»)),
             panLang$One)) |+
           («g», ([], panLang$Return (panLang$Const (7w:8 word)), panLang$One)))))``

val _ = print_eval "nested_deccall_code_map_clock_8"
  ``(FST (panSem$evaluate
      (panLang$DecCall «answer» panLang$One «f» []
        (panLang$Return (panLang$Var panLang$Local «answer»)),
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («f», ([],
             panLang$DecCall «nested» panLang$One «g» []
               (panLang$Return (panLang$Var panLang$Local «nested»)),
             panLang$One)) |+
           («g», ([], panLang$Return (panLang$Const (7w:8 word)), panLang$One))))),
     (SND (panSem$evaluate
      (panLang$DecCall «answer» panLang$One «f» []
        (panLang$Return (panLang$Var panLang$Local «answer»)),
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («f», ([],
             panLang$DecCall «nested» panLang$One «g» []
               (panLang$Return (panLang$Var panLang$Local «nested»)),
             panLang$One)) |+
           («g», ([], panLang$Return (panLang$Const (7w:8 word)), panLang$One)))))).clock)``

(* Negative recursive dispatch rows: the callee state is retained on a
   return-shape error, including its decremented clock and cleared locals. *)
val bad_call_return_shape_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («keep», ValWord (42w:8 word));
      code := FEMPTY |+ («bad», ([],
        panLang$Return (panLang$Const (7w:8 word)), panLang$Comb []));
      clock := 10 |>)``;

val _ = print_eval "recursive_call_bad_return_shape"
  ``case panSem$evaluate (panLang$Call NONE «bad» [],
      ^bad_call_return_shape_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «keep»)``

val bad_deccall_declared_shape_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («keep», ValWord (42w:8 word));
      code := FEMPTY |+ («bad», ([],
        panLang$Return (panLang$Const (7w:8 word)), panLang$One));
      clock := 10 |>)``;

val _ = print_eval "recursive_deccall_bad_declared_shape"
  ``case panSem$evaluate
      (panLang$DecCall «answer» (panLang$Comb []) «bad» [] panLang$Skip,
       ^bad_deccall_declared_shape_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «keep»)``

val recursive_missing_code_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («x», ValWord (7w:8 word));
      code := FEMPTY; clock := 5 |>)``;

val _ = print_eval "recursive_call_missing_function"
  ``case panSem$evaluate
      (panLang$Call NONE «missing» [], ^recursive_missing_code_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «x»)``

val _ = print_eval "recursive_deccall_missing_function"
  ``case panSem$evaluate
      (panLang$DecCall «answer» panLang$One «missing» [] panLang$Skip,
       ^recursive_missing_code_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «x»)``

val recursive_bad_argument_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («x», ValWord (7w:8 word));
      code := FEMPTY |+ («id», ([], panLang$Skip, panLang$One));
      clock := 10 |>)``;

val _ = print_eval "recursive_call_bad_argument"
  ``case panSem$evaluate
      (panLang$Call NONE «id» [panLang$Var panLang$Local «absent»],
       ^recursive_bad_argument_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «x»)``

val _ = print_eval "recursive_deccall_bad_argument"
  ``case panSem$evaluate
      (panLang$DecCall «answer» panLang$One «id»
        [panLang$Var panLang$Local «absent»] panLang$Skip,
       ^recursive_bad_argument_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «x»)``

val recursive_call_destination_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («answer», ValWord (3w:8 word));
      code := FEMPTY |+ («id», ([(«x», panLang$One)],
        panLang$Return (panLang$Var panLang$Local «x»), panLang$One));
      clock := 10 |>)``;

val _ = print_eval "recursive_call_destination_success"
  ``case panSem$evaluate
      (panLang$Call (SOME (SOME (panLang$Local, «answer»), NONE)) «id»
        [panLang$Const (7w:8 word)], ^recursive_call_destination_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «answer»)``

val _ = print_eval "recursive_call_destination_shape_error"
  ``case panSem$evaluate
      (^bad_destination_call_program, ^bad_destination_call_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «answer»)``

(* Negative recursive dispatch rows for Call control and exception handling. *)
val recursive_skip_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («keep», ValWord (42w:8 word));
      code := FEMPTY |+ («skip», ([], panLang$Skip, panLang$One));
      clock := 10 |>)``;

val _ = print_eval "recursive_call_callee_skip"
  ``case panSem$evaluate (panLang$Call NONE «skip» [], ^recursive_skip_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «keep»)``

val _ = print_eval "recursive_deccall_callee_skip"
  ``case panSem$evaluate
      (panLang$DecCall «answer» panLang$One «skip» [] panLang$Skip,
       ^recursive_skip_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «keep»)``

val recursive_break_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («keep», ValWord (42w:8 word));
      code := FEMPTY |+ («break», ([], panLang$Break, panLang$One));
      clock := 10 |>)``;

val _ = print_eval "recursive_call_callee_break"
  ``case panSem$evaluate (panLang$Call NONE «break» [], ^recursive_break_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «keep»)``

val _ = print_eval "recursive_deccall_callee_break"
  ``case panSem$evaluate
      (panLang$DecCall «answer» panLang$One «break» [] panLang$Skip,
       ^recursive_break_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «keep»)``

val recursive_continue_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («keep», ValWord (42w:8 word));
      code := FEMPTY |+ («continue», ([], panLang$Continue, panLang$One));
      clock := 10 |>)``;

val _ = print_eval "recursive_call_callee_continue"
  ``case panSem$evaluate
      (panLang$Call NONE «continue» [], ^recursive_continue_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «keep»)``

val _ = print_eval "recursive_deccall_callee_continue"
  ``case panSem$evaluate
      (panLang$DecCall «answer» panLang$One «continue» [] panLang$Skip,
       ^recursive_continue_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «keep»)``

val recursive_wrong_exception_handler_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («caught», ValWord (0w:8 word));
      eshapes := FEMPTY |+ («E», panLang$One) |+ («F», panLang$One);
      code := FEMPTY |+ («raiseF», ([],
        panLang$Raise «F» (panLang$Const (7w:8 word)), panLang$One));
      clock := 10 |>)``;

val _ = print_eval "recursive_call_nonmatching_exception_handler"
  ``case panSem$evaluate
      (panLang$Call (SOME (NONE, SOME («E», «caught», panLang$Skip)))
        «raiseF» [], ^recursive_wrong_exception_handler_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «caught»)``

val recursive_invalid_exception_target_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («caught», RStruct []);
      eshapes := FEMPTY |+ («E», panLang$One);
      code := FEMPTY |+ («raiseE», ([],
        panLang$Raise «E» (panLang$Const (7w:8 word)), panLang$One));
      clock := 10 |>)``;

val _ = print_eval "recursive_call_invalid_exception_target"
  ``case panSem$evaluate
      (panLang$Call (SOME (NONE, SOME («E», «caught», panLang$Skip)))
        «raiseE» [], ^recursive_invalid_exception_target_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «caught»)``

val recursive_deccall_exception_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («keep», ValWord (42w:8 word));
      eshapes := FEMPTY |+ («E», panLang$One);
      code := FEMPTY |+ («raiseE», ([],
        panLang$Raise «E» (panLang$Const (7w:8 word)), panLang$One));
      clock := 10 |>)``;

val _ = print_eval "recursive_deccall_exception_propagates"
  ``case panSem$evaluate
      (panLang$DecCall «answer» panLang$One «raiseE» [] panLang$Skip,
       ^recursive_deccall_exception_state) of
      (res, s') => (res, s'.clock, FLOOKUP s'.locals «keep»)``

val _ = print_eval "nested_call_code_map_7"
  ``FST (panSem$evaluate
      (panLang$Call NONE «f» [],
       (((ARB:((8),unit) panSem$state) with clock := 10) with
         code := FEMPTY |+
           («f», ([], panLang$Call NONE «g» [], panLang$One)) |+
           («g», ([], panLang$Return (panLang$Const (7w:8 word)), panLang$One)))))``

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

val _ = print_eval "call_record_first_field_7"
  ``FST (panSem$evaluate
      (panLang$Call NONE «id»
        [panLang$RField 0 (panLang$Var panLang$Local «pair»)],
       ((ARB:((8),unit) panSem$state) with
        <| locals := FEMPTY |+ («pair», RStruct [ValWord (7w:8 word);
               ValWord (8w:8 word)]);
         code := FEMPTY |+
           («id», ([(«x», panLang$One)],
             panLang$Return (panLang$Var panLang$Local «x»), panLang$One));
             clock := 10 |>)))``

val _ = print_eval "call_record_middle_pair_7_8"
  ``FST (panSem$evaluate
      (panLang$Call NONE «pair»
        [panLang$RField 1 (panLang$Var panLang$Local «record»)],
       ((ARB:((8),unit) panSem$state) with
        <| locals := FEMPTY |+ («record», RStruct [ValWord (3w:8 word);
               RStruct [ValWord (7w:8 word); ValWord (8w:8 word)];
               ValWord (10w:8 word)]);
         code := FEMPTY |+
           («pair», ([(«p», panLang$Comb [panLang$One; panLang$One])],
             panLang$Return (panLang$Var panLang$Local «p»),
             panLang$Comb [panLang$One; panLang$One]));
         clock := 10 |>)))``

val _ = print_eval "call_constructed_record_middle_pair_7_8"
  ``FST (panSem$evaluate
      (panLang$Call NONE «pair»
        [panLang$RField 1
          (panLang$RStruct [panLang$Const (3w:8 word);
            panLang$RStruct [panLang$Const (7w:8 word);
              panLang$Const (8w:8 word)];
            panLang$Const (10w:8 word)])],
       ((ARB:((8),unit) panSem$state) with <|
         code := FEMPTY |+
           («pair», ([(«p», panLang$Comb [panLang$One; panLang$One])],
             panLang$Return (panLang$Var panLang$Local «p»),
             panLang$Comb [panLang$One; panLang$One]));
         clock := 10 |>)))``

val _ = print_eval "call_struct_field_rfield_7_8"
  ``FST (panSem$evaluate
      (panLang$Call NONE «pair»
        [panLang$RStruct
          [panLang$RField 0
            (panLang$RStruct [panLang$Const (7w:8 word);
              panLang$Const (9w:8 word)]);
           panLang$Const (8w:8 word)]],
       (((ARB:((8),unit) panSem$state) with
          code := FEMPTY |+
            («pair», ([(«p», panLang$Comb [panLang$One; panLang$One])],
              panLang$Return (panLang$Var panLang$Local «p»),
              panLang$Comb [panLang$One; panLang$One]))) with clock := 10)))``

val _ = print_eval "call_nested_struct_field_rfield_7_8"
  ``FST (panSem$evaluate
      (panLang$Call NONE «nestedPair»
        [panLang$RStruct
          [panLang$RStruct
            [panLang$RField 0
              (panLang$RStruct [panLang$Const (7w:8 word);
                panLang$Const (9w:8 word)])];
           panLang$Const (8w:8 word)]],
       (((ARB:((8),unit) panSem$state) with
          code := FEMPTY |+
            («nestedPair», ([(«p», panLang$Comb
              [panLang$Comb [panLang$One]; panLang$One])],
              panLang$Return (panLang$Var panLang$Local «p»),
              panLang$Comb [panLang$Comb [panLang$One]; panLang$One])))
          with clock := 10)))``

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

(* Direct Return/Raise/Dec clause probes: success and failure.
   Reference: panSemScript.sml:556-561 (Dec), :625-630 (Return/Raise). *)
val _ = print_eval "return_clears_locals"
  ``(FST (panSem$evaluate
      (panLang$Return (panLang$Const (41w:8 word)),
       ((ARB:((8),unit) panSem$state) with
          locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word))))),
     FLOOKUP (SND (panSem$evaluate
      (panLang$Return (panLang$Const (41w:8 word)),
       ((ARB:((8),unit) panSem$state) with
          locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word)))))).locals
       (strlit "x"))``

val _ = print_eval "return_shape_too_big"
  ``FST (panSem$evaluate
      (panLang$Return
         (panLang$RStruct
            (GENLIST (K (panLang$Const (0w:8 word))) 33)),
       (ARB:((8),unit) panSem$state)))``

val _ = print_eval "raise_clears_locals"
  ``(FST (panSem$evaluate
      (panLang$Raise «E» (panLang$Const (5w:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word));
          eshapes := FEMPTY |+ («E», panLang$One) |>))),
     FLOOKUP (SND (panSem$evaluate
      (panLang$Raise «E» (panLang$Const (5w:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word));
          eshapes := FEMPTY |+ («E», panLang$One) |>)))).locals (strlit "x"))``

val _ = print_eval "raise_missing_exception"
  ``FST (panSem$evaluate
      (panLang$Raise «E» (panLang$Const (5w:8 word)),
       ((ARB:((8),unit) panSem$state) with eshapes := FEMPTY)))``

val _ = print_eval "raise_shape_mismatch"
  ``FST (panSem$evaluate
      (panLang$Raise «E» (panLang$NStruct «big» []),
       ((ARB:((8),unit) panSem$state) with <|
          structs := [];
          eshapes := FEMPTY |+ («E», panLang$One) |>)))``

val _ = print_eval "dec_restores_locals"
  ``(FST (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Const (9w:8 word))
         (panLang$Return (panLang$Var panLang$Local (strlit "x"))),
       ((ARB:((8),unit) panSem$state) with
          locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word))))),
     FLOOKUP (SND (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Const (9w:8 word))
         (panLang$Return (panLang$Var panLang$Local (strlit "x"))),
       ((ARB:((8),unit) panSem$state) with
          locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word)))))).locals
       (strlit "x"))``

val _ = print_eval "dec_shape_mismatch"
  ``FST (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$RStruct [])
         panLang$Skip,
       (ARB:((8),unit) panSem$state)))``

val _ = print_eval "dec_missing_old_binding"
  ``(FST (panSem$evaluate
      (panLang$Dec (strlit "fresh") panLang$One (panLang$Const (9w:8 word))
         panLang$Skip,
       ((ARB:((8),unit) panSem$state) with
          locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word))))),
     FLOOKUP (SND (panSem$evaluate
      (panLang$Dec (strlit "fresh") panLang$One (panLang$Const (9w:8 word))
         panLang$Skip,
       ((ARB:((8),unit) panSem$state) with
          locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word)))))).locals
       (strlit "fresh"))``

val _ = print_eval "dec_break_restores_locals"
  ``(FST (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Const (9w:8 word))
         panLang$Break,
       ((ARB:((8),unit) panSem$state) with
          locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word))))),
     FLOOKUP (SND (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Const (9w:8 word))
         panLang$Break,
       ((ARB:((8),unit) panSem$state) with
          locals := FEMPTY |+ (strlit "x", ValWord (7w:8 word)))))).locals
       (strlit "x"))``

val _ = print_eval "dec_missing_local_break"
  ``(FST (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Const (9w:8 word))
         panLang$Break,
       ((ARB:((8),unit) panSem$state) with locals := FEMPTY))),
     FLOOKUP (SND (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Const (9w:8 word))
         panLang$Break,
       ((ARB:((8),unit) panSem$state) with locals := FEMPTY)))).locals
       (strlit "x"))``

val _ = print_eval "dec_missing_local_continue"
  ``(FST (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Const (9w:8 word))
         panLang$Continue,
       ((ARB:((8),unit) panSem$state) with locals := FEMPTY))),
     FLOOKUP (SND (panSem$evaluate
      (panLang$Dec (strlit "x") panLang$One (panLang$Const (9w:8 word))
         panLang$Continue,
       ((ARB:((8),unit) panSem$state) with locals := FEMPTY)))).locals
       (strlit "x"))``

val _ = print_eval "nb_op_op8" ``nb_op Op8``

val _ = print_eval "nb_op_op16" ``nb_op Op16``

val _ = print_eval "nb_op_opW" ``nb_op OpW``

val _ = print_eval "nb_op_op32" ``nb_op Op32``

val _ = print_eval "lookup_kvar_local"
  ``lookup_kvar Local (strlit "x")
      ((ARB:((8),unit) panSem$state) with
         locals := FEMPTY |+ (strlit "x", ValWord (3w:8 word)))``

val _ = print_eval "lookup_kvar_global"
  ``lookup_kvar Global (strlit "y")
      ((ARB:((8),unit) panSem$state) with
         globals := FEMPTY |+ (strlit "y", ValWord (4w:8 word)))``

val _ = print_eval "lookup_kvar_missing"
  ``lookup_kvar Local (strlit "z")
      ((ARB:((8),unit) panSem$state) with locals := FEMPTY)``

val returning_ffi =
  ``<| oracle := (λname st conf bytes. ffi$Oracle_return st (MAP (λb. (0x42w:word8)) bytes));
      ffi_state := (); io_events := [] |>``;

val _ = print_eval "shmemload_returned"
  ``case panSem$evaluate
      (panLang$ShMemLoad OpW Local «v» (panLang$Const (8w:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («v», ValWord (0w:8 word));
          sh_memaddrs := {8w}; ffi := ^returning_ffi |>)) of
      (res,s') => (res, FLOOKUP s'.locals «v»)``

val _ = print_eval "shmemload_missing_local"
  ``case panSem$evaluate
      (panLang$ShMemLoad OpW Local «v» (panLang$Const (8w:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY;
          sh_memaddrs := {8w}; ffi := ^returning_ffi |>)) of
      (res,s') => res``

val _ = print_eval "shmemload_out_of_domain"
  ``case panSem$evaluate
      (panLang$ShMemLoad OpW Local «v» (panLang$Const (8w:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («v», ValWord (0w:8 word));
          sh_memaddrs := EMPTY; ffi := ^returning_ffi |>)) of
      (res,s') => res``

val _ = print_eval "shmemstore_returned"
  ``case panSem$evaluate
      (panLang$ShMemStore OpW (panLang$Const (8w:8 word))
         (panLang$Const (0xABw:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          sh_memaddrs := {8w}; ffi := ^returning_ffi |>)) of
      (res,s') => res``

val _ = print_eval "shmemstore_out_of_domain"
  ``case panSem$evaluate
      (panLang$ShMemStore OpW (panLang$Const (8w:8 word))
         (panLang$Const (0xABw:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          sh_memaddrs := EMPTY; ffi := ^returning_ffi |>)) of
      (res,s') => res``

val _ = print_eval "while_cond_zero"
  ``case panSem$evaluate
      (panLang$While (panLang$Const (0w:8 word)) panLang$Skip,
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY; structs := []; clock := 5 |>)) of
      (res,s') => (res, s'.clock)``

val _ = print_eval "while_timeout"
  ``case panSem$evaluate
      (panLang$While (panLang$Const (1w:8 word)) panLang$Skip,
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (0w:8 word)); structs := []; clock := 0 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x»)``

val _ = print_eval "while_break"
  ``case panSem$evaluate
      (panLang$While (panLang$Var Local «x») panLang$Break,
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (1w:8 word)); structs := []; clock := 5 |>)) of
      (res,s') => (res, s'.clock, FLOOKUP s'.locals «x»)``

val _ = print_eval "while_continue_then_zero"
  ``case panSem$evaluate
      (panLang$While (panLang$Var Local «x»)
         (panLang$Assign Local «x» (panLang$Const (0w:8 word))),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (1w:8 word)); structs := []; clock := 5 |>)) of
      (res,s') => (res, s'.clock, FLOOKUP s'.locals «x»)``

val _ = print_eval "while_error_condition"
  ``case panSem$evaluate
      (panLang$While (panLang$Var Local «missing») panLang$Skip,
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY; structs := []; clock := 5 |>)) of
      (res,s') => res``

val _ = print_eval "while_skip_timeout"
  ``case panSem$evaluate
      (panLang$While (panLang$Const (1w:8 word)) panLang$Skip,
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (1w:8 word)); structs := []; clock := 1 |>)) of
      (res,s') => (res, s'.clock, FLOOKUP s'.locals «x»)``

val _ = print_eval "while_continue_timeout"
  ``case panSem$evaluate
      (panLang$While (panLang$Const (1w:8 word)) panLang$Continue,
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (1w:8 word)); structs := []; clock := 1 |>)) of
      (res,s') => (res, s'.clock, FLOOKUP s'.locals «x»)``

val _ = print_eval "while_return_propagates"
  ``case panSem$evaluate
      (panLang$While (panLang$Const (1w:8 word))
         (panLang$Return (panLang$Const (9w:8 word))),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (1w:8 word)); structs := []; clock := 5 |>)) of
      (res,s') => (res, s'.clock, FLOOKUP s'.locals «x»)``

val _ = print_eval "dec_clock_step"
  ``panSem$dec_clock ((ARB:((8),unit) panSem$state) with <| clock := 5 |>)``

val _ = print_eval "fix_clock_clamps"
  ``case panSem$fix_clock
      ((ARB:((8),unit) panSem$state) with <| clock := 2 |>)
      (NONE, ((ARB:((8),unit) panSem$state) with <| clock := 7 |>)) of
      (res,s') => (res, s'.clock)``

val _ = print_eval "fix_clock_keeps_new"
  ``case panSem$fix_clock
      ((ARB:((8),unit) panSem$state) with <| clock := 9 |>)
      (NONE, ((ARB:((8),unit) panSem$state) with <| clock := 4 |>)) of
      (res,s') => (res, s'.clock)``

val _ = print_eval "isWord_def_word" ``panSem$isWord (Word (3w:8 word))``

val _ = print_eval "theWord_def_word" ``panSem$theWord (Word (3w:8 word))``

val _ = print_eval "assign_local_ok"
  ``case panSem$evaluate
      (panLang$Assign Local «x» (panLang$Const (9w:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (7w:8 word)); globals := FEMPTY; structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x»)``

val _ = print_eval "assign_global_ok"
  ``case panSem$evaluate
      (panLang$Assign Global «g» (panLang$Const (9w:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY; globals := FEMPTY |+ («g», ValWord (1w:8 word)); structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.globals «g»)``

val _ = print_eval "assign_shape_mismatch"
  ``case panSem$evaluate
      (panLang$Assign Local «x» (panLang$RStruct []),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (7w:8 word)); structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x»)``

val _ = print_eval "assign_expr_error"
  ``case panSem$evaluate
      (panLang$Assign Local «x» (panLang$Var Local «missing»),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (7w:8 word)); structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x»)``

val _ = print_eval "primitive_success"
  ``case panSem$evaluate
      (panLang$Primitive «x» AddCarry
         [panLang$Const (40w:8 word); panLang$Const (50w:8 word); panLang$Const (0w:8 word)],
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», RStruct [ValWord (0w:8 word); ValWord (0w:8 word)]);
          structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x»)``

val _ = print_eval "primitive_shape_mismatch"
  ``case panSem$evaluate
      (panLang$Primitive «x» AddCarry
         [panLang$Const (40w:8 word); panLang$Const (50w:8 word); panLang$Const (0w:8 word)],
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (7w:8 word)); structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x»)``

val _ = print_eval "primitive_wrong_args"
  ``case panSem$evaluate
      (panLang$Primitive «x» AddCarry
         [panLang$Const (1w:8 word); panLang$Const (2w:8 word)],
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», RStruct [ValWord (0w:8 word); ValWord (0w:8 word)]);
          structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x»)``

val _ = print_eval "primitive_arg_error"
  ``case panSem$evaluate
      (panLang$Primitive «x» AddCarry
         [panLang$Const (1w:8 word); panLang$Var Local «missing»; panLang$Const (0w:8 word)],
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», RStruct [ValWord (0w:8 word); ValWord (0w:8 word)]);
          structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x»)``


val _ = print_eval "store_clause_hit"
  ``case panSem$evaluate
      (panLang$Store (panLang$Const (0w:64 word)) (panLang$Const (7w:64 word)),
       ((ARB:((64),unit) panSem$state) with
          <| memaddrs := {0w}; memory := (\a:64 word. Word (0w:64 word)); be := F |>)) of
      (res, s') => (res, s'.memory 0w)``

val _ = print_eval "store_clause_out_of_domain"
  ``case panSem$evaluate
      (panLang$Store (panLang$Const (0w:64 word)) (panLang$Const (7w:64 word)),
       ((ARB:((64),unit) panSem$state) with
          <| memaddrs := {}; memory := (\a:64 word. Word (0w:64 word)) |>)) of
      (res, s') => (res, s'.memory 0w)``

val _ = print_eval "store32_clause_hit"
  ``case panSem$evaluate
      (panLang$Store32 (panLang$Const (0w:64 word)) (panLang$Const (0x11223344w:64 word)),
       ((ARB:((64),unit) panSem$state) with
          <| memaddrs := {0w}; memory := (\a:64 word. Word (0w:64 word)); be := F |>)) of
      (res, s') => (res, s'.memory 0w)``

val _ = print_eval "storebyte_clause_hit"
  ``case panSem$evaluate
      (panLang$StoreByte (panLang$Const (0w:64 word)) (panLang$Const (0xABw:64 word)),
       ((ARB:((64),unit) panSem$state) with
          <| memaddrs := {0w}; memory := (\a:64 word. Word (0w:64 word)); be := F |>)) of
      (res, s') => (res, s'.memory 0w)``

val _ = print_eval "tick_clock_zero"
  ``case panSem$evaluate
      (panLang$Tick,
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (7w:8 word)); clock := 0 |>)) of
      (res, s') => (res, FLOOKUP s'.locals «x», s'.clock)``

val _ = print_eval "tick_clock_positive"
  ``case panSem$evaluate
      (panLang$Tick,
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (7w:8 word)); clock := 5 |>)) of
      (res, s') => (res, FLOOKUP s'.locals «x», s'.clock)``

val final_ffi =
  ``<| oracle := (λname st conf bytes. ffi$Oracle_final ffi$FFI_failed);
      ffi_state := (); io_events := [] |>``;

val _ = print_eval "extcall_clause_returned"
  ``case panSem$evaluate
      (panLang$ExtCall «x» (panLang$Const (0w:8 word)) (panLang$Const (2w:8 word))
         (panLang$Const (0w:8 word)) (panLang$Const (2w:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY;
          memory := (\a:8 word. if a = 0w then Word (0xABw:8 word) else Word (0w:8 word));
          memaddrs := {0w; 1w}; sh_memaddrs := EMPTY; be := F;
          ffi := ^returning_ffi |>)) of
      (res, s') => (res, s'.memory 0w)``

val _ = print_eval "extcall_clause_bad_read"
  ``case panSem$evaluate
      (panLang$ExtCall «x» (panLang$Const (0w:8 word)) (panLang$Const (2w:8 word))
         (panLang$Const (0w:8 word)) (panLang$Const (2w:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY;
          memory := (\a:8 word. if a = 0w then Word (0xABw:8 word) else Word (0w:8 word));
          memaddrs := EMPTY; sh_memaddrs := EMPTY; be := F;
          ffi := ^returning_ffi |>)) of
      (res, s') => (res, s'.memory 0w)``

val _ = print_eval "extcall_clause_final"
  ``case panSem$evaluate
      (panLang$ExtCall «x» (panLang$Const (0w:8 word)) (panLang$Const (2w:8 word))
         (panLang$Const (0w:8 word)) (panLang$Const (2w:8 word)),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (7w:8 word));
          memory := (\a:8 word. if a = 0w then Word (0xABw:8 word) else Word (0w:8 word));
          memaddrs := {0w; 1w}; sh_memaddrs := EMPTY; be := F;
          ffi := ^final_ffi |>)) of
      (res, s') => (case res of SOME (FinalFFI _) => (T, FLOOKUP s'.locals «x») | _ => (F, FLOOKUP s'.locals «x»))``

val dec_call_code =
  ``FEMPTY |+ («f», ([(«a», panLang$One)],
      panLang$Return (panLang$Var panLang$Local «a»), panLang$One))``;

val _ = print_eval "lookup_code_ok"
  ``case panSem$lookup_code ^dec_call_code «f» [ValWord (3w:8 word)] of
      SOME (_, ls, _) => (T, FLOOKUP ls «a») | NONE => (F, NONE)``

val _ = print_eval "lookup_code_bad_arg"
  ``case panSem$lookup_code ^dec_call_code «f» [panSem$RStruct []] of
      SOME (_, ls, _) => (T, FLOOKUP ls «a») | NONE => (F, NONE)``

val _ = print_eval "lookup_code_dup_param"
  ``case panSem$lookup_code
      (FEMPTY |+ («f», ([(«a», panLang$One); («a», panLang$One)],
        panLang$Skip, panLang$One))) «f» [ValWord (3w:8 word)] of
      SOME (_, ls, _) => (T, FLOOKUP ls «a») | NONE => (F, NONE)``

val dec_call_state_5 =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («r», ValWord (0w:8 word));
      code := FEMPTY |+ («f», ([(«a», panLang$One)],
        panLang$Return (panLang$Var panLang$Local «a»), panLang$One));
      clock := 5 |>)``;

val dec_call_state_0 =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («r», ValWord (0w:8 word));
      code := FEMPTY |+ («f», ([(«a», panLang$One)],
        panLang$Return (panLang$Var panLang$Local «a»), panLang$One));
      clock := 0 |>)``;

val dec_call_state_missing =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («r», ValWord (0w:8 word));
      code := FEMPTY; clock := 5 |>)``;

val _ = print_eval "deccall_clause_ok"
  ``case panSem$evaluate
      (panLang$DecCall «r» panLang$One «f» [panLang$Const (3w:8 word)]
         (panLang$Return (panLang$Var panLang$Local «r»)),
       ^dec_call_state_5) of
      (res, s') => (res, FLOOKUP s'.locals «r», FLOOKUP s'.locals «a»)``

val _ = print_eval "deccall_clause_clock_zero"
  ``case panSem$evaluate
      (panLang$DecCall «r» panLang$One «f» [panLang$Const (3w:8 word)]
         (panLang$Return (panLang$Var panLang$Local «r»)),
       ^dec_call_state_0) of
      (res, s') => (res, FLOOKUP s'.locals «r», s'.clock)``

val _ = print_eval "deccall_clause_bad_shape"
  ``case panSem$evaluate
      (panLang$DecCall «r» (panLang$Comb []) «f» [panLang$Const (3w:8 word)]
         (panLang$Return (panLang$Var panLang$Local «r»)),
       ^dec_call_state_5) of
      (res, s') => (res, FLOOKUP s'.locals «r»)``

val _ = print_eval "deccall_clause_missing_function"
  ``case panSem$evaluate
      (panLang$DecCall «r» panLang$One «g» [panLang$Const (3w:8 word)]
         (panLang$Return (panLang$Var panLang$Local «r»)),
       ^dec_call_state_missing) of
      (res, s') => (res, FLOOKUP s'.locals «r»)``

val call_state_5 =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («r», ValWord (0w:8 word)) |+ («ev», ValWord (0w:8 word));
      code := FEMPTY |+ («f», ([(«a», panLang$One)],
          panLang$Return (panLang$Var panLang$Local «a»), panLang$One))
                     |+ («g», ([(«a», panLang$One)],
          panLang$Raise «E» (panLang$Var panLang$Local «a»), panLang$One));
      eshapes := FEMPTY |+ («E», panLang$One);
      clock := 5 |>)``;

val call_state_0 =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («r», ValWord (0w:8 word));
      code := FEMPTY |+ («f», ([(«a», panLang$One)],
          panLang$Return (panLang$Var panLang$Local «a»), panLang$One));
      clock := 0 |>)``;

val call_state_badshape =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY;
      code := FEMPTY |+ («f», ([(«a», panLang$One)],
          panLang$Return (panLang$RStruct []), panLang$One));
      clock := 5 |>)``;

val _ = print_eval "call_clause_ok_none"
  ``case panSem$evaluate
      (panLang$Call NONE «f» [panLang$Const (3w:8 word)], ^call_state_5) of
      (res, s') => (res, FLOOKUP s'.locals «a», FLOOKUP s'.locals «r»)``

val _ = print_eval "call_clause_ok_nodest"
  ``case panSem$evaluate
      (panLang$Call (SOME (NONE, NONE)) «f» [panLang$Const (3w:8 word)], ^call_state_5) of
      (res, s') => (res, FLOOKUP s'.locals «a», FLOOKUP s'.locals «r»)``

val _ = print_eval "call_clause_ok_dest"
  ``case panSem$evaluate
      (panLang$Call (SOME (SOME (panLang$Local, «r»), NONE)) «f» [panLang$Const (3w:8 word)],
       ^call_state_5) of
      (res, s') => (res, FLOOKUP s'.locals «r»)``

val _ = print_eval "call_clause_bad_shape"
  ``case panSem$evaluate
      (panLang$Call NONE «f» [panLang$Const (3w:8 word)], ^call_state_badshape) of
      (res, s') => (res, FLOOKUP s'.locals «a»)``

val _ = print_eval "call_clause_handler"
  ``case panSem$evaluate
      (panLang$Call (SOME (NONE, SOME («E», «ev», panLang$Skip))) «g»
         [panLang$Const (3w:8 word)], ^call_state_5) of
      (res, s') => (res, FLOOKUP s'.locals «ev»)``

val _ = print_eval "call_clause_missing_function"
  ``case panSem$evaluate
      (panLang$Call NONE «h» [panLang$Const (3w:8 word)], ^call_state_5) of
      (res, s') => (res, FLOOKUP s'.locals «r»)``

val _ = print_eval "call_clause_clock_zero"
  ``case panSem$evaluate
      (panLang$Call NONE «f» [panLang$Const (3w:8 word)], ^call_state_0) of
      (res, s') => (res, FLOOKUP s'.locals «a»)``


val _ = print_eval "seq_two_assigns"
  ``case panSem$evaluate
      (panLang$Seq (panLang$Assign Local «x» (panLang$Const (1w:8 word)))
         (panLang$Assign Local «x» (panLang$Const (2w:8 word))),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (0w:8 word)); structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x», s'.clock)``

val _ = print_eval "seq_first_errors"
  ``case panSem$evaluate
      (panLang$Seq (panLang$Assign Local «x» (panLang$Var Local «missing»))
         (panLang$Assign Local «x» (panLang$Const (2w:8 word))),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («x», ValWord (0w:8 word)); structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x»)``

val recursive_seq_call_normal_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («answer», ValWord (0w:8 word));
      code := FEMPTY |+ («id», ([(«x», panLang$One)],
        panLang$Return (panLang$Var Local «x»), panLang$One));
      clock := 10 |>)``;

val _ = print_eval "recursive_seq_call_normal_continue"
  ``case panSem$evaluate
      (panLang$Seq
        (panLang$Call (SOME (NONE, NONE)) «id» [panLang$Const (7w:8 word)])
        (panLang$Return (panLang$Const (9w:8 word))),
       ^recursive_seq_call_normal_state) of
      (res,s') => (res, s'.clock, FLOOKUP s'.locals «answer»)``

val recursive_seq_call_error_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («answer», ValWord (0w:8 word));
      code := FEMPTY |+ («skip», ([], panLang$Skip, panLang$One));
      clock := 10 |>)``;

val _ = print_eval "recursive_seq_call_terminal_error"
  ``case panSem$evaluate
      (panLang$Seq
        (panLang$Call (SOME (NONE, NONE)) «skip» [])
        (panLang$Return (panLang$Const (9w:8 word))),
       ^recursive_seq_call_error_state) of
      (res,s') => (res, s'.clock, FLOOKUP s'.locals «answer»)``

val _ = print_eval "if_true"
  ``case panSem$evaluate
      (panLang$If (panLang$Var Local «c»)
         (panLang$Assign Local «x» (panLang$Const (1w:8 word)))
         (panLang$Assign Local «x» (panLang$Const (2w:8 word))),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («c», ValWord (1w:8 word)) |+ («x», ValWord (0w:8 word));
          structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x»)``

val _ = print_eval "if_false"
  ``case panSem$evaluate
      (panLang$If (panLang$Var Local «c»)
         (panLang$Assign Local «x» (panLang$Const (1w:8 word)))
         (panLang$Assign Local «x» (panLang$Const (2w:8 word))),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY |+ («c», ValWord (0w:8 word)) |+ («x», ValWord (0w:8 word));
          structs := []; clock := 5 |>)) of
      (res,s') => (res, FLOOKUP s'.locals «x»)``

val _ = print_eval "if_error"
  ``case panSem$evaluate
      (panLang$If (panLang$Var Local «missing») panLang$Skip panLang$Skip,
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY; structs := []; clock := 5 |>)) of
      (res,s') => res``

val _ = print_eval "break_clause"
  ``case panSem$evaluate
      (panLang$Break,
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY; structs := []; clock := 5 |>)) of
      (res,s') => (res, s'.clock)``

val _ = print_eval "continue_clause"
  ``case panSem$evaluate
      (panLang$Continue,
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY; structs := []; clock := 5 |>)) of
      (res,s') => (res, s'.clock)``

val _ = print_eval "annot_clause"
  ``case panSem$evaluate
      (panLang$Annot (strlit "t") (strlit "u"),
       ((ARB:((8),unit) panSem$state) with <|
          locals := FEMPTY; structs := []; clock := 5 |>)) of
      (res,s') => (res, s'.clock)``

val semantics_decls_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY; globals := FEMPTY; structs := []; code := FEMPTY;
      eshapes := FEMPTY; clock := 5 |>):((8),unit) panSem$state``

val _ = print_eval "semantics_decls_bad_struct"
  ``panSem$semantics_decls ^semantics_decls_state «main»
      [panLang$Name «S» [(«f», panLang$Named «Missing»)]]``

val _ = print_eval "semantics_decls_bad_function"
  ``panSem$semantics_decls ^semantics_decls_state «main»
      [panLang$Function <|
         name := «f»; inline := F; export := F;
         params := [(«x», panLang$Named «Missing»)];
         body := panLang$Skip; return := panLang$One |>]``

val _ = print_eval "semantics_decls_bad_exception"
  ``panSem$semantics_decls ^semantics_decls_state «main»
      [panLang$ExnDecl «E» (panLang$Named «Missing»)]``

val ivs_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («x», ValWord (7w:8 word));
      globals := FEMPTY |+ («g», ValWord (9w:8 word));
      clock := 5 |>):((8),unit) panSem$state``

val ivs_clock_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («x», ValWord (7w:8 word));
      globals := FEMPTY |+ («g», ValWord (9w:8 word));
      clock := 9 |>):((8),unit) panSem$state``

val ivs_memory_state =
  ``((ARB:((8),unit) panSem$state) with <|
      locals := FEMPTY |+ («x», ValWord (7w:8 word));
      globals := FEMPTY |+ («g», ValWord (9w:8 word));
      memory := (\a. Word (a:8 word)); clock := 5 |>):((8),unit) panSem$state``

val _ = print_eval "kvar_simps_set_local"
  ``panSem$set_kvar Local «x» (ValWord (3w:8 word)) ^ivs_state =
    panSem$set_var «x» (ValWord (3w:8 word)) ^ivs_state``

val _ = print_eval "kvar_simps_lookup_local"
  ``panSem$lookup_kvar Local «x» ^ivs_state = SOME (ValWord (7w:8 word))``

val _ = print_eval "is_valid_value_clock_update"
  ``panSem$is_valid_value ^ivs_clock_state Local «x» (ValWord (7w:8 word)) =
    panSem$is_valid_value ^ivs_state Local «x» (ValWord (7w:8 word))``

val _ = print_eval "is_valid_value_memory_update"
  ``panSem$is_valid_value ^ivs_memory_state Local «x» (ValWord (7w:8 word)) =
    panSem$is_valid_value ^ivs_state Local «x» (ValWord (7w:8 word))``

val _ = print_eval "kvar_defs_set_kvar_local"
  ``panSem$set_kvar Local «x» (ValWord (3w:8 word)) ^ivs_state =
    panSem$set_var «x» (ValWord (3w:8 word)) ^ivs_state``

val _ = print_eval "kvar_defs_set_global_update"
  ``FLOOKUP (panSem$set_global «g» (ValWord (3w:8 word)) ^ivs_state).globals «g»
      = SOME (ValWord (3w:8 word)) /\
    FLOOKUP (panSem$set_global «g» (ValWord (3w:8 word)) ^ivs_state).locals «x»
      = SOME (ValWord (7w:8 word))``

val _ = print_eval "kvar_defs_lookup_global"
  ``panSem$lookup_kvar Global «g» ^ivs_state = SOME (ValWord (9w:8 word))``

val _ = print_eval "kvar_defs_is_valid_value"
  ``panSem$is_valid_value ^ivs_state Local «x» (ValWord (7w:8 word)) =
    (panSem$shape_of (ValWord (7w:8 word)) =
     panSem$shape_of (ValWord (7w:8 word)))``

val vshapes_args_ex = ``[(strlit "a", One)] : (mlstring # shape) list``;
val vshapes_args_vals = ``[ValWord (3w : 8 word)] : 8 panSem$v list``;
val _ = print_eval "vshapes_args_rel_ok" ``LIST_REL (\vshape arg. SND vshape = shape_of arg) ^vshapes_args_ex ^vshapes_args_vals``;
val _ = print_eval "vshapes_args_rel_concl" ``(LENGTH ^vshapes_args_ex = LENGTH ^vshapes_args_vals) /\ (MAP SND ^vshapes_args_ex = MAP shape_of ^vshapes_args_vals)``;
val _ = print_eval "vshapes_args_rel_mismatch" ``LIST_REL (\vshape arg. SND vshape = shape_of arg) ^vshapes_args_ex [(RStruct [] : 8 panSem$v)]``;
val _ = print_eval "pan_sem_e2e_done" ``0``
