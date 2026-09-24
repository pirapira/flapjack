(* Direct HOL-EVAL observations for pan_to_crep$alookup_compile_prog_code.
   Reference: cakeml/pancake/proofs/pan_to_crepProofScript.sml:4575. *)
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

(* A single function with empty params and body Skip: the compiled entry must
   be found under the same name with `crep_vars [] = []` argument slots. *)
val _ = print_eval "alookup_empty_params"
  ``case ALOOKUP (pan_to_crep$compile_to_crep
       ([panLang$Function
          <| name := «f»; inline := F; export := F; params := [];
             body := panLang$Skip; return := panLang$One |>]
        : (8 word) panLang$decl list)) «f» of
      SOME ([], body) => T | _ => F``;

(* The source function list is distinct, so the HOL premise holds and the
   looked-up entry really is the compiled function. *)
val _ = print_eval "source_names_distinct"
  ``ALL_DISTINCT (MAP FST (MAP (λd. (d, ())) [])) = T``;

(* A function with nonempty params is still found, but its slot list is
   `crep_vars [("x",One)] = [0]`, not `[]`. *)
val _ = print_eval "alookup_param_entry"
  ``case ALOOKUP (pan_to_crep$compile_to_crep
       ([panLang$Function
          <| name := «g»; inline := F; export := F;
             params := [(«x», panLang$One)];
             body := panLang$Skip; return := panLang$One |>]
        : (8 word) panLang$decl list)) «g» of
      SOME ([0], body) => T | _ => F``;