(*
  Direct HOL observations for h_prog_primitive_def.
  Reference: cakeml/pancake/semantics/pan_itreeSemScript.sml:264-275.
*)
load "bossLib";
load "preamble";
load "pan_itreeSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_itreeSemTheory;

val s = ``(s:(8) pan_itreeSem$bstate)``;
val base = ``(^s with locals := (FEMPTY : (mlstring |-> 8 v)) |+
    (strlit "dst", RStruct [ValWord 0w; ValWord 0w]))``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "primitive_success"
  ``case h_prog_primitive (strlit "dst") panLang$AddCarry
      [panLang$Const (40w:8 word); panLang$Const (50w:8 word);
       panLang$Const (0w:8 word)] ^base of
      | itreeTau$Ret (INR (NONE,s')) =>
          FLOOKUP s'.locals (strlit "dst") =
            SOME (RStruct [ValWord 90w; ValWord 0w])
      | _ => F``;

val _ = print_eval "primitive_wrong_args"
  ``case h_prog_primitive (strlit "dst") panLang$AddCarry
      [panLang$Const (40w:8 word); panLang$Const (50w:8 word)] ^base of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;

val _ = print_eval "primitive_missing_operand"
  ``case h_prog_primitive (strlit "dst") panLang$AddCarry
      [panLang$Const (40w:8 word);
       panLang$Var panLang$Local (strlit "missing");
       panLang$Const (0w:8 word)] ^base of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;

val _ = print_eval "primitive_shape_error"
  ``case h_prog_primitive (strlit "other") panLang$AddCarry
      [panLang$Const (40w:8 word); panLang$Const (50w:8 word);
       panLang$Const (0w:8 word)] ^base of
      | itreeTau$Ret (INR (SOME Error,s')) => T
      | _ => F``;
