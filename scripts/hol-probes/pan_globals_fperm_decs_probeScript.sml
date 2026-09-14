(* Direct HOL-EVAL fixture for pan_globals$fperm_decs_def. *)
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

val _ = print_eval "mixed"
  ``pan_globals$fperm_decs «foo» «bar»
      [panLang$Decl panLang$One «g» (panLang$Const 7w);
       panLang$Function <| name := «foo»; inline := F; export := T;
         params := []; body := panLang$Call NONE «foo» [];
         return := panLang$One |>;
       panLang$Function <| name := «bar»; inline := T; export := F;
         params := []; body := panLang$DecCall «x» panLang$One «foo» [] panLang$Skip;
         return := panLang$One |> ]``;
val _ = print_eval "empty"
  ``pan_globals$fperm_decs «foo» «bar» []``;
