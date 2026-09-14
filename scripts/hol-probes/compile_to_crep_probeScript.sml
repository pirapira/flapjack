(* Direct HOL-EVAL probes for pan_to_crep$compile_to_crep.
   Reference: cakeml/pancake/pan_to_crepScript.sml:383-391. *)
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
  ``pan_to_crep$compile_to_crep
      ([] : (8 word) panLang$decl list)``;

val _ = print_eval "raise_const"
  ``pan_to_crep$compile_to_crep
      [panLang$ExnDecl «E» panLang$One;
       panLang$Function
         <| name := «f»; inline := F; export := F;
            params := [(«x», panLang$One)];
            body := panLang$Raise «E» (panLang$Const (7w : 8 word));
            return := panLang$One |>]``;
