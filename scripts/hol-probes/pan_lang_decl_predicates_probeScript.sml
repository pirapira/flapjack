(*
  Direct HOL-EVAL observations for Pancake panLang declaration predicates.
  Reference: cakeml/pancake/panLangScript.sml:234-253.
*)
load "bossLib";
load "preamble";
load "panLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val declaration = ``Decl One (strlit "g") (Const 7w)``;
val exception_declaration = ``ExnDecl (strlit "E") One``;
val name_declaration = ``Name (strlit "S") []``;

val _ = print_eval "is_decl_decl" ``is_decl ^declaration``;
val _ = print_eval "is_decl_exception" ``is_decl ^exception_declaration``;
val _ = print_eval "is_exn_decl_exception" ``is_exn_decl ^exception_declaration``;
val _ = print_eval "is_exn_decl_decl" ``is_exn_decl ^declaration``;
val _ = print_eval "is_name_name" ``is_name ^name_declaration``;
val _ = print_eval "is_name_decl" ``is_name ^declaration``;
val _ = print_eval "size_of_eids_empty"
  ``size_of_eids ([] : (word64 panLang$decl) list)``;
val _ = print_eval "size_of_eids_mixed"
  ``size_of_eids [^declaration; ^name_declaration; ^exception_declaration]``;
