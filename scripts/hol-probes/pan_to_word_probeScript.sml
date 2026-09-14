(*
  Probe outputs for the original CakeML Pancake pan_to_word definitions.
  This is intentionally a HOL script rather than a second implementation.
  The checked-in output is captured from a direct HOL invocation.
*)
load "bossLib";
load "preamble";
load "pan_to_wordTheory";
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

val _ = print_eval "compile_empty"
  ``pan_to_word$compile_prog RISC_V
      ([] : (8 word) panLang$decl list)``
val _ = print_eval "compile_skip_main"
  ``pan_to_word$compile_prog RISC_V
      [panLang$Function
        <| name := «main»; inline := F; export := F; params := [];
           body := panLang$Skip; return := panLang$One |>]``

val _ = print_eval "stage_pan_simp"
  ``pan_simp$compile_prog
      [panLang$Function
        <| name := «main»; inline := F; export := F; params := [];
           body := panLang$Skip; return := panLang$One |>]``
val _ = print_eval "stage_pan_structs"
  ``pan_structs$compile_top
      (pan_simp$compile_prog
        [panLang$Function
          <| name := «main»; inline := F; export := F; params := [];
             body := panLang$Skip; return := panLang$One |>])``
val _ = print_eval "stage_pan_globals"
  ``pan_globals$compile_top
      (pan_structs$compile_top
        (pan_simp$compile_prog
          [panLang$Function
            <| name := «main»; inline := F; export := F; params := [];
               body := panLang$Skip; return := panLang$One |>])) «main»``
val _ = print_eval "stage_pan_to_crep"
  ``pan_to_crep$compile_prog
      (pan_globals$compile_top
        (pan_structs$compile_top
          (pan_simp$compile_prog
            [panLang$Function
              <| name := «main»; inline := F; export := F; params := [];
                 body := panLang$Skip; return := panLang$One |>])) «main»)``
val _ = print_eval "stage_crep_to_loop"
  ``crep_to_loop$compile_prog RISC_V
      (pan_to_crep$compile_prog
        (pan_globals$compile_top
          (pan_structs$compile_top
            (pan_simp$compile_prog
              [panLang$Function
                <| name := «main»; inline := F; export := F; params := [];
                   body := panLang$Skip; return := panLang$One |>])) «main»))``
