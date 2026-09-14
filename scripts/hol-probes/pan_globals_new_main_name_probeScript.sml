(* Direct HOL-EVAL fixture for pan_globals$new_main_name_def. *)
load "bossLib";
load "preamble";
load "pan_globalsTheory";
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
  end

val _ = print_eval "empty"
  ``pan_globals$new_main_name []``;
val _ = print_eval "two_collisions"
  ``pan_globals$new_main_name
      [panLang$Function <| name := «main»; inline := F; export := F;
         params := []; body := panLang$Skip; return := panLang$One |>;
       panLang$Function <| name := «main'»; inline := F; export := F;
         params := []; body := panLang$Skip; return := panLang$One |> ]``;
val _ = print_eval "mixed"
  ``pan_globals$new_main_name
      [panLang$Decl panLang$One «g» (panLang$Const 7w);
       panLang$Name «S» []; panLang$ExnDecl «E» panLang$One;
       panLang$Function <| name := «main»; inline := F; export := F;
         params := []; body := panLang$Skip; return := panLang$One |> ]``;
val _ = print_eval "absent"
  ``pan_globals$new_main_name
      [panLang$Function <| name := «worker»; inline := F; export := F;
         params := []; body := panLang$Skip; return := panLang$One |> ]``;
