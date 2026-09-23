(* Direct HOL-EVAL fixture for pan_globals$compile_decs_def. *)
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

val ctxt =
  ``((<| globals := FEMPTY; globals_size := 1w; max_globals_size := 16w |> ) :
      8 word pan_globals$context)``;
val _ = print_eval "empty"
  ``pan_globals$compile_decs ^ctxt ([] : 8 word panLang$decl list)``;
val _ = print_eval "decl"
  ``pan_globals$compile_decs ^ctxt
      [panLang$Decl One «g» (panLang$Const 7w)]``;
val _ = print_eval "exception"
  ``pan_globals$compile_decs ^ctxt
      [panLang$ExnDecl «E» One]``;
val _ = print_eval "name"
  ``pan_globals$compile_decs ^ctxt
      [panLang$Name «S» []]``;

(* Function-before-Decl: the function body must be compiled under the context
   as of its own position, so the later «g» declaration is NOT yet visible and
   the global read becomes Const 0w.  The function-after-decl row resolves it. *)
val functionDecl =
  ``(<| name := «f»; inline := F; export := F; params := [];
        body := panLang$Assign panLang$Local «x» (panLang$Var panLang$Global «g»);
        return := One |>) : 8 word panLang$fun_decl``;
val _ = print_eval "function_before_decl"
  ``pan_globals$compile_decs ^ctxt
      [panLang$Function ^functionDecl;
       panLang$Decl One «g» (panLang$Const 7w)]``;
val _ = print_eval "function_after_decl"
  ``pan_globals$compile_decs ^ctxt
      [panLang$Decl One «g» (panLang$Const 7w);
       panLang$Function ^functionDecl]``;
