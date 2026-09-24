(* Direct HOL-EVAL observations for pan_to_crep$make_funcs (make_funcs_def,
   cakeml/pancake/pan_to_crepScript.sml:366), a definition unfolded by HOL
   mk_ctxt_code_imp_code_rel (pan_to_crepProofScript.sml:4604).

   The rows evaluate make_funcs on the ACTUAL function table of one declaration
   list and compare the looked-up parameter list and return shape exactly. *)
load "bossLib";
load "preamble";
load "../pan_to_crepTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open pan_to_crepTheory;
open finite_mapTheory;

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

val _ = print_eval "make_funcs_empty_params"
  ``FLOOKUP (make_funcs (functions ^decls)) «f» = SOME ([], One)``;

val _ = print_eval "make_funcs_param_entry"
  ``FLOOKUP (make_funcs (functions ^decls)) «g» = SOME ([(«x», One)], One)``;

val _ = print_eval "make_funcs_absent"
  ``FLOOKUP (make_funcs (functions ^decls)) «h» = NONE``;

(* `alist_to_fmap` keeps the FIRST duplicate binding; make_funcs inherits that. *)
val dupDecls = ``([panLang$Function
                     <| name := «f»; inline := F; export := F; params := [];
                        body := panLang$Skip; return := panLang$One |>;
                   panLang$Function
                     <| name := «f»; inline := F; export := F;
                        params := [(«y», panLang$One)];
                        body := panLang$Skip; return := panLang$One |>]
                 : (8 word) panLang$decl list)``;

val _ = print_eval "make_funcs_duplicate_first_wins"
  ``FLOOKUP (make_funcs (functions ^dupDecls)) «f» = SOME ([], One)``;