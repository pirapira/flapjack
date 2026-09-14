(* Direct HOL-EVAL fixture for pan_globals$compile_top_def. *)
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

val _ = print_eval "missing"
  ``pan_globals$compile_top
      [panLang$Function <| name := «main»; inline := F; export := F;
         params := []; body := panLang$Skip; return := panLang$One |>]
      «absent»``;
val _ = print_eval "simple"
  ``pan_globals$compile_top
      [panLang$Function <| name := «main»; inline := F; export := F;
         params := []; body := panLang$Skip; return := panLang$One |>]
      «main»``;
