(*
  Direct HOL observations for pan_globalsProof$MEM_functions.
  Reference: cakeml/pancake/proofs/pan_globalsProofScript.sml:2380-2387.

  `MEM_functions` is declared `[local]`, so it is not exported to the theory
  database and cannot be fetched by name.  The rows below instead directly
  evaluate the underlying `functions` projection and the membership shape that
  the theorem describes.
*)
load "bossLib";
load "preamble";
load "panLangTheory";
load "pan_globalsProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;
open pan_globalsProofTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val function_decl =
  ``(Function <| name := strlit "f"; inline := T; export := F;
                 params := [(strlit "x", One)]; body := Skip;
                 return := One |> : (8 word) panLang$decl)``;
val global_decl = ``Decl One (strlit "g") (Const (7w : 8 word))``;

val _ = print_eval "functions_empty" ``functions ([] : (8 word) panLang$decl list)``;
val _ = print_eval "functions_function" ``functions [^function_decl]``;
val _ = print_eval "functions_global" ``functions [^global_decl]``;
val _ = print_eval "mem_function_entry"
  ``MEM (strlit "f",[(strlit "x",One)],Skip,One) (functions [^function_decl])``;
