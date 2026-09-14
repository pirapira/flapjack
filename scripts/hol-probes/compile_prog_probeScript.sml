(* Direct HOL-EVAL probes for pan_to_crep$compile_prog.
   Reference: cakeml/pancake/pan_to_crepScript.sml:393-398. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "empty"
  ``pan_to_crep$compile_prog
      ([] : (8 word) panLang$decl list)``;

val _ = print_eval "inline_call"
  ``pan_to_crep$compile_prog
      [panLang$Function
         <| name := «id»; inline := T; export := F;
            params := []; body := panLang$Return (panLang$Const (7w : 8 word));
            return := panLang$One |>;
       panLang$Function
         <| name := «main»; inline := F; export := T;
            params := []; body := panLang$Call NONE «id» [];
            return := panLang$One |>]``;
