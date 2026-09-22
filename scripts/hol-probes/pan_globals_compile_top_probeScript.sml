(* Direct HOL-EVAL fixture for pan_globals$compile_top, including its
   missing-start fallback to the empty declaration list. *)
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

val main =
  ``panLang$Function
      <| name := «main»; inline := F; export := F; params := [];
         body := panLang$Skip; return := panLang$One |>``

val _ = print_eval "missing_start"
  ``pan_globals$compile_top [^main] «absent»``;

val _ = print_eval "present_start"
  ``pan_globals$compile_top [^main] «main»``;
