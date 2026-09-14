(* Direct HOL-EVAL fixture for pan_globals$dec_shapes_def. *)
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
  ``pan_globals$dec_shapes []``;
val _ = print_eval "mixed"
  ``pan_globals$dec_shapes
      [panLang$Function <| name := «f»; inline := F; export := F;
         params := []; body := panLang$Skip; return := panLang$One |>;
       panLang$Decl (panLang$Comb [panLang$One; panLang$Named «S»])
         «g» (panLang$Const 7w);
       panLang$Name «S» [];
       panLang$ExnDecl «E» (panLang$Named «T»);
       panLang$Decl panLang$One «h» (panLang$Const 9w)]``;
