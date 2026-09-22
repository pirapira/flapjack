(* Direct HOL-EVAL probes for CakeML Pancake panSem$evaluate_decls_def. *)
load "bossLib";
load "preamble";
load "panSemTheory";
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

val s = ``(s:('a,'ffi) panSem$state)``;
val state0 = ``(^s with <| locals := FEMPTY; globals := FEMPTY;
                            structs := []; code := FEMPTY;
                            eshapes := FEMPTY |>)``;
val fun_decl = ``<| name := strlit "f"; inline := F; export := F;
                    params := [(strlit "x", One)]; body := Skip;
                    return := One |>``;

val _ = print_eval "empty" ``evaluate_decls ^state0 []``
val _ = print_eval "name_noop"
  ``case evaluate_decls ^state0 [Name (strlit "S") []] of
      SOME s' => (s'.structs, s'.globals, s'.code, s'.eshapes)
    | NONE => ARB``
val _ = print_eval "decl_global_update"
  ``case evaluate_decls ^state0 [Decl One (strlit "g") (Const 7w)] of
      SOME s' => (FLOOKUP s'.globals (strlit "g"), s'.locals)
    | NONE => ARB``
val _ = print_eval "decl_word_load_update"
  ``case evaluate_decls (^state0 with <|
        memaddrs := {0w}; memory := (\x. if x = 0w then Word 9w else ARB) |>)
      [Decl One (strlit "g") (Load One (Const 0w))] of
      SOME s' => FLOOKUP s'.globals (strlit "g")
    | NONE => ARB``
val _ = print_eval "decl_bad_load_shape"
  ``evaluate_decls ^state0
      [Decl One (strlit "g") (Load (Named (strlit "Missing")) (Const 0w))]``
val _ = print_eval "decl_preserves_locals"
  ``case evaluate_decls (^state0 with
        locals := FUPDATE FEMPTY (strlit "x", ValWord 3w))
      [Decl One (strlit "g") (Const 7w)] of
      SOME s' => (FLOOKUP s'.globals (strlit "g"),
                  FLOOKUP s'.locals (strlit "x"))
    | NONE => ARB``
val _ = print_eval "decl_left_to_right"
  ``case evaluate_decls ^state0
      [Decl One (strlit "g") (Const 7w);
       Decl One (strlit "h") (Var Global (strlit "g"))] of
      SOME s' => (FLOOKUP s'.globals (strlit "g"),
                  FLOOKUP s'.globals (strlit "h"))
    | NONE => ARB``
val _ = print_eval "decl_empty_locals_failure"
  ``evaluate_decls (^state0 with locals := FUPDATE FEMPTY (strlit "x", ValWord 3w))
      [Decl One (strlit "g") (Var Local (strlit "x"))]``
val _ = print_eval "decl_shape_failure"
  ``evaluate_decls ^state0 [Decl (Named (strlit "Missing"))
      (strlit "g") (Const 7w)]``
val _ = print_eval "function_code_update"
  ``case evaluate_decls ^state0 [Function ^fun_decl] of
      SOME s' => FLOOKUP s'.code (strlit "f")
    | NONE => ARB``
val _ = print_eval "function_code_replacement"
  ``case evaluate_decls (^state0 with
        code := FUPDATE FEMPTY (strlit "f", ([], Skip, One)))
      [Function ^fun_decl] of
      SOME s' => FLOOKUP s'.code (strlit "f")
    | NONE => ARB``
val _ = print_eval "function_bad_param_shape"
  ``evaluate_decls ^state0 [Function
      (^fun_decl with params := [(strlit "x", Named (strlit "Missing"))])]``
val _ = print_eval "function_bad_return_shape"
  ``evaluate_decls ^state0 [Function
      (^fun_decl with return := Named (strlit "Missing"))]``
val _ = print_eval "exn_shape_update"
  ``case evaluate_decls ^state0 [ExnDecl (strlit "E") One] of
      SOME s' => FLOOKUP s'.eshapes (strlit "E")
    | NONE => ARB``
val _ = print_eval "exn_duplicate_failure"
  ``evaluate_decls (^state0 with eshapes := FUPDATE FEMPTY (strlit "E", One))
      [ExnDecl (strlit "E") One]``
val _ = print_eval "exn_bad_shape_failure"
  ``evaluate_decls ^state0 [ExnDecl (strlit "E") (Named (strlit "Missing"))]``
