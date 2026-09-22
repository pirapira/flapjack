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

val _ = print_eval "raise_pair"
  ``pan_to_crep$compile_to_crep
      [panLang$ExnDecl «E» (panLang$Comb [panLang$One; panLang$One]);
       panLang$Function
         <| name := «f»; inline := F; export := F; params := [];
            body := panLang$Raise «E»
              (panLang$RStruct
                [panLang$Const (7w : 8 word); panLang$Const 9w]);
            return := panLang$One |>]``;

val _ = print_eval "handled_pair"
  ``pan_to_crep$compile_to_crep
      [panLang$ExnDecl «E» (panLang$Comb [panLang$One; panLang$One]);
        panLang$Function
          <| name := «f»; inline := F; export := F; params := [];
             body := panLang$Raise «E»
               (panLang$RStruct
                 [panLang$Const (7w : 8 word); panLang$Const 9w]);
             return := panLang$Comb [panLang$One; panLang$One] |>;
        panLang$Function
          <| name := «g»; inline := F; export := F;
             params := [(«pair», panLang$Comb [panLang$One; panLang$One])];
             body := panLang$Call
               (SOME
                 (SOME (panLang$Local, «pair»),
                  SOME («E», «pair», panLang$Skip)))
               «f» [];
             return := panLang$One |>]``;

val _ = print_eval "done" ``T``;
