(* Direct HOL-EVAL observations for pan_to_crep$alookup_compile_prog_code.
   Reference: cakeml/pancake/proofs/pan_to_crepProofScript.sml:4575.

   These rows use the ACTUAL source function list of one declaration list and
   compare the looked-up body to `comp_func (make_funcs (functions decls))
   (get_eids_from_decls decls) ...`, i.e. the exact HOL conclusion, rather than
   a shape test. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

(* One declaration list with an empty-parameter `f` and a one-parameter `g`. *)
val decls = ``([panLang$Function
                  <| name := «f»; inline := F; export := F; params := [];
                     body := panLang$Skip; return := panLang$One |>;
                panLang$Function
                  <| name := «g»; inline := F; export := F;
                     params := [(«x», panLang$One)];
                     body := panLang$Skip; return := panLang$One |>]
              : (8 word) panLang$decl list)``;

(* The source function names of THIS declaration list are distinct, so the HOL
   theorem's premise holds. *)
val _ = print_eval "source_names_distinct"
  ``ALL_DISTINCT (MAP FST (functions ^decls))``;

(* Empty-parameter entry: the looked-up body is EXACTLY the HOL comp_func
   result for `[]` and `Skip`. *)
val _ = print_eval "alookup_empty_params"
  ``case ALOOKUP (compile_to_crep ^decls) «f» of
      SOME ([], body) =>
        (body = comp_func (make_funcs (functions ^decls))
                  (get_eids_from_decls ^decls) [] Skip)
    | _ => F``;

(* Nonempty-parameter entry: again exact body equality, and the slot list is
   `crep_vars [("x",One)] = [0]`, not `[]`. *)
val _ = print_eval "alookup_param_entry"
  ``case ALOOKUP (compile_to_crep ^decls) «g» of
      SOME ([0], body) =>
        (body = comp_func (make_funcs (functions ^decls))
                  (get_eids_from_decls ^decls) [(«x», One)] Skip)
    | _ => F``;