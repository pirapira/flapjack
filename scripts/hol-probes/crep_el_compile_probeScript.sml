(* Direct HOL-EVAL observations for pan_to_crep$el_compile_prog_el_prog_eq.
   Reference: cakeml/pancake/proofs/pan_to_crepProofScript.sml:4589.

   These rows use the ACTUAL source function list of one declaration list: the
   source table entry at index 0, its ALOOKUP, and the compiled entry at index
   0 reduced to the exact HOL comp_func body, rather than a shape test. *)
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

(* One declaration list with an empty-parameter `f` and a one-parameter `g`,
   so index 0 is `f` and the names are distinct. *)
val decls = ``([panLang$Function
                  <| name := «f»; inline := F; export := F; params := [];
                     body := panLang$Skip; return := panLang$One |>;
                panLang$Function
                  <| name := «g»; inline := F; export := F;
                     params := [(«x», panLang$One)];
                     body := panLang$Skip; return := panLang$One |>]
              : (8 word) panLang$decl list)``;

(* The source entry at index 0 is exactly `f` with empty params, body Skip,
   return One. *)
val _ = print_eval "source_el_f"
  ``EL 0 (functions ^decls) = («f», [], panLang$Skip, panLang$One)``;

(* The ALOOKUP of `f` in the source table yields the same triple. *)
val _ = print_eval "alookup_f"
  ``ALOOKUP (functions ^decls) «f» = SOME ([], panLang$Skip, panLang$One)``;

(* The compiled entry at index 0 has the same name and empty slots, and its
   body is EXACTLY the HOL comp_func result for `[]` and `Skip`. *)
val _ = print_eval "compiled_el_f"
  ``EL 0 (compile_to_crep ^decls) =
      («f», [],
       comp_func (make_funcs (functions ^decls))
         (get_eids_from_decls ^decls) [] panLang$Skip)``;