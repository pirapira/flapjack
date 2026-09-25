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

val _ = print_eval "pan_sem_e2e_done" ``0``
