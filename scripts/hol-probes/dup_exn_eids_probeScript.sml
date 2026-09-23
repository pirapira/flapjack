(* Direct HOL-EVAL probes for repeated exception declarations at the
   Pan-to-Crep executable boundary.
   Reference: cakeml/pancake/pan_to_crepScript.sml:356-391
   (`get_eids_from_decls_def`, `compile_to_crep_def`).

   `get_eids_from_decls` numbers every exception declaration in source order
   and folds the result with `alist_to_fmap`, whose evaluation returns the
   *first* binding for a repeated key (unlike `FEMPTY |++`, used by
   `make_vmap`, which keeps the later binding).  A repeated exception name
   therefore resolves to the ID of its first declaration, and the emitted
   `Raise` code uses that ID. *)
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

val _ = print_eval "dup_eids_lookup"
  ``FLOOKUP
      (pan_to_crep$get_eids_from_decls
        ([panLang$ExnDecl «E» panLang$One;
          panLang$ExnDecl «E» panLang$One] : (8 word) panLang$decl list))
      «E»``;

val _ = print_eval "mixed_eids_lookup_a"
  ``FLOOKUP
      (pan_to_crep$get_eids_from_decls
        ([panLang$ExnDecl «A» panLang$One;
          panLang$ExnDecl «E» panLang$One;
          panLang$ExnDecl «E» panLang$One] : (8 word) panLang$decl list))
      «A»``;

val _ = print_eval "mixed_eids_lookup_e"
  ``FLOOKUP
      (pan_to_crep$get_eids_from_decls
        ([panLang$ExnDecl «A» panLang$One;
          panLang$ExnDecl «E» panLang$One;
          panLang$ExnDecl «E» panLang$One] : (8 word) panLang$decl list))
      «E»``;

val _ = print_eval "dup_compile"
  ``pan_to_crep$compile_to_crep
      [panLang$ExnDecl «E» panLang$One;
       panLang$ExnDecl «E» panLang$One;
       panLang$Function
         <| name := «f»; inline := F; export := F; params := [];
            body := panLang$Raise «E» (panLang$Const (7w : 8 word));
            return := panLang$One |>]``;

val _ = print_eval "done" ``T``;