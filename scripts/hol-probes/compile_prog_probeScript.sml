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

val _ = print_eval "duplicate_first"
  ``pan_to_crep$compile_prog
      [panLang$Function
         <| name := «id»; inline := T; export := F;
            params := []; body := panLang$Return (panLang$Const (7w : 8 word));
            return := panLang$One |>;
       panLang$Function
         <| name := «id»; inline := T; export := F;
            params := []; body := panLang$Return (panLang$Const (9w : 8 word));
            return := panLang$One |>;
       panLang$Function
         <| name := «main»; inline := F; export := T;
            params := []; body := panLang$Call NONE «id» [];
            return := panLang$One |>]``;

val _ = print_eval "nested_inline"
  ``pan_to_crep$compile_prog
      [panLang$Function
         <| name := «leaf»; inline := T; export := F;
            params := []; body := panLang$Return (panLang$Const (7w : 8 word));
            return := panLang$One |>;
       panLang$Function
         <| name := «mid»; inline := T; export := F;
            params := []; body := panLang$Call NONE «leaf» [];
            return := panLang$One |>;
       panLang$Function
         <| name := «main»; inline := F; export := T;
            params := []; body := panLang$Call NONE «mid» [];
            return := panLang$One |>]``;

val _ = print_eval "global_dest"
  ``pan_to_crep$compile_to_crep
      ([panLang$Function
          <| name := «f»; inline := F; export := F; params := [];
             body := panLang$Skip;
             return := panLang$Comb [panLang$One; panLang$One] |>;
        panLang$Function
          <| name := «g»; inline := F; export := F;
             params := [(«pair», panLang$Comb [panLang$One; panLang$One])];
             body := panLang$Call
               (SOME (SOME (panLang$Global, «pair»), NONE)) «f» [];
             return := panLang$One |>]
       : (8 word) panLang$decl list)``;

val _ = print_eval "handled_missing_dest"
  ``pan_to_crep$compile_to_crep
      ([panLang$ExnDecl «E» (panLang$Comb [panLang$One; panLang$One]);
        panLang$Function
          <| name := «f»; inline := F; export := F; params := [];
             body := panLang$Skip;
             return := panLang$Comb [panLang$One; panLang$One] |>;
        panLang$Function
          <| name := «g»; inline := F; export := F;
             params := [(«pair», panLang$Comb [panLang$One; panLang$One])];
             body := panLang$Call
               (SOME
                 (SOME (panLang$Local, «missing»),
                  SOME («E», «pair», panLang$Skip)))
               «f» [];
             return := panLang$One |>]
       : (8 word) panLang$decl list)``;

val _ = print_eval "done" ``T``;
