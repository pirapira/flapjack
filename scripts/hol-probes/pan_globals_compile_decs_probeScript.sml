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
(* Direct compile_exp/compile fixtures.  `ctxt` has an empty globals map, so a
   global read misses and becomes Const 0w; `ctxtWithGlobal` binds «g» to
   (One,7w), so the same read resolves to Load One (Op Sub [TopAddr; Const 7w]). *)
val ctxtWithGlobal =
  ``((<| globals := FEMPTY |+ («g»,(One,7w)) |+ («r»,(One,7w)); globals_size := 1w;
        max_globals_size := 16w |> ) : 8 word pan_globals$context)``;
val _ = print_eval "compile_exp_top"
  ``pan_globals$compile_exp ^ctxt (panLang$TopAddr)``;
val _ = print_eval "compile_exp_global_miss"
  ``pan_globals$compile_exp ^ctxt (panLang$Var panLang$Global «g»)``;
val _ = print_eval "compile_exp_global_hit"
  ``pan_globals$compile_exp ^ctxtWithGlobal (panLang$Var panLang$Global «g»)``;
val _ = print_eval "compile_exp_nstruct"
  ``pan_globals$compile_exp ^ctxt (panLang$NStruct «S» [])``;
val _ = print_eval "compile_assign_global_hit"
  ``pan_globals$compile ^ctxtWithGlobal
      (panLang$Assign panLang$Global «g» (panLang$Const 5w))``;
val _ = print_eval "compile_assign_global_miss"
  ``pan_globals$compile ^ctxt
      (panLang$Assign panLang$Global «g» (panLang$Const 5w))``;

(* Direct compile_def handled-Global full-program fixture.  The destination
   «r» is a Global bound to (One,7w), so compile takes the FLOOKUP hit branch
   with an exception handler, producing the whole nested Dec/Seq/Call/If/Store
   program.  The handler body mentions local «vn'», so the fresh-name machinery
   is exercised: names = [«ev»;«x»;«vn'»], vn' = «», flag = «vn''».  The
   argument reads global «g» and is compiled to Load One (Op Sub [...]). *)
val handledHandler =
  ``(panLang$Seq
      (panLang$Assign panLang$Local «x» (panLang$Const 1w))
      (panLang$Assign panLang$Local «vn'» (panLang$Const 2w))) :
      (8 word) panLang$prog``;
val handledCall =
  ``(panLang$Call
      (SOME (SOME (panLang$Global, «r»),
             SOME («e», «ev», ^handledHandler)))
      «f»
      ([panLang$Var panLang$Global «g»] : (8 word) panLang$exp list)) :
      (8 word) panLang$prog``;
val _ = print_eval "compile_def_handled_global"
  ``pan_globals$compile ^ctxtWithGlobal ^handledCall``;

(* Direct fresh_name fixtures: append one apostrophe per collision. *)
val _ = print_eval "fresh_name_clear"
  ``pan_globals$fresh_name «x» [«y»]``;
val _ = print_eval "fresh_name_missing_empty"
  ``pan_globals$fresh_name «» ([] : mlstring list)``;
val _ = print_eval "fresh_name_hit"
  ``pan_globals$fresh_name «» [«»; «'»; «''»]``;
val _ = print_eval "fresh_name_seed"
  ``pan_globals$fresh_name «vn'» [«vn'»]``;

(* Sentinel so the multi-line `function_after_decl` value above is not the last
   label; regenerate.sh captures rows up to the last label and would drop the
   continuation lines of a row that wraps. *)
val _ = print_eval "compile_decs_probe_done" ``0``;
