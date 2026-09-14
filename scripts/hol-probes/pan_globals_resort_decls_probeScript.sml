(* Direct HOL-EVAL fixture for pan_globals$resort_decls_def. *)
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
  ``pan_globals$resort_decls
      [panLang$Decl One «g» (panLang$Const 7w);
       panLang$Name «S» []; panLang$ExnDecl «E» One]``;
val _ = print_eval "stable_groups"
  ``pan_globals$resort_decls
      [panLang$Name «S1» []; panLang$Name «S2» [];
       panLang$ExnDecl «E1» One; panLang$ExnDecl «E2» One;
       panLang$Decl One «g1» (panLang$Const 1w);
       panLang$Decl One «g2» (panLang$Const 2w)]``;
