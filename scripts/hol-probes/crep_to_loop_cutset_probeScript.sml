(* Direct HOL-EVAL fixture for crep_to_loop$compile statement-region
   live-set threading into Call cutsets, If branches, While bodies, and
   Dec continuations.
   Reference: cakeml/pancake/crep_to_loopScript.sml compile_def. *)
load "bossLib";
load "preamble";
load "crep_to_loopTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end

val ctxt =
  ``<| vars := (FEMPTY |+ (1,5)); funcs := FEMPTY |+ («f»,(64,0));
      vmax := 10; target := RISC_V |>``;

val ctxt_dec =
  ``<| vars := (FEMPTY |+ (1,5)); funcs := FEMPTY;
      vmax := 4; target := RISC_V |>``;

val ctxt_shmem =
  ``<| vars := (FEMPTY |+ (3,8)); funcs := FEMPTY;
      vmax := 0; target := RISC_V |>``;

(* Dec must rename the bound source variable to the fresh temporary used by
   the expression compiler and retain that mapping in the continuation. *)
val _ = print_eval "dec_renaming"
  ``crep_to_loop$compile ^ctxt_dec (insert 5 () LN)
      (crepLang$Dec 9 (crepLang$Const (7w : 8 word))
         (crepLang$Assign 9 (crepLang$Var 9)))``;

(* A shared-memory operation also uses nested_seq over its generated list. *)
val _ = print_eval "shmem_nested_seq"
  ``crep_to_loop$compile ^ctxt_shmem LN
      (crepLang$ShMem Store 3 (crepLang$Var 1))``;

(* Incoming statement-region live set {5}.  The Call cutset must be built
   from this ORIGINAL live set; argument-expression temps are excluded. *)
val _ = print_eval "cut_set_const_args"
  ``crep_to_loop$compile ^ctxt (insert 5 () LN)
      (crepLang$Call (SOME ([1],NONE)) «f»
         [crepLang$Const (1w : 8 word); crepLang$Const (2w : 8 word)])``;

(* The argument expression consumes temp 11 and adds it to compile_exps'
   accumulated live set nl; the cutset must still use the original {5}. *)
val _ = print_eval "cut_set_load32_arg"
  ``crep_to_loop$compile ^ctxt (insert 5 () LN)
      (crepLang$Call (SOME ([1],NONE)) «f»
         [crepLang$Load32 (crepLang$Const (0w : 8 word))])``;

(* Dec inserts the fresh destination temp 11 into the continuation's live
   set; the inner Call cutset must be built from {5, 11}. *)
val _ = print_eval "dec_continuation_live"
  ``crep_to_loop$compile ^ctxt (insert 5 () LN)
      (crepLang$Dec 1 (crepLang$Const (7w : 8 word))
         (crepLang$Call (SOME ([1],NONE)) «f» [crepLang$Var 1]))``;

(* If branches are compiled with the ORIGINAL live set {5}, not with the
   condition temp 11 added. *)
val _ = print_eval "if_branches_original_live"
  ``crep_to_loop$compile ^ctxt (insert 5 () LN)
      (crepLang$If (crepLang$Load32 (crepLang$Const (0w : 8 word)))
         (crepLang$Call (SOME ([1],NONE)) «f» [crepLang$Const (1w : 8 word)])
         (crepLang$Call (SOME ([1],NONE)) «f» [crepLang$Const (2w : 8 word)]))``;

(* While body and the loop's live annotations use the ORIGINAL live set. *)
val _ = print_eval "while_body_original_live"
  ``crep_to_loop$compile ^ctxt (insert 5 () LN)
      (crepLang$While (crepLang$Load32 (crepLang$Const (0w : 8 word)))
         (crepLang$Call (SOME ([1],NONE)) «f» [crepLang$Const (1w : 8 word)]))``;

(* Handler code is compiled with the ORIGINAL live set {5}. *)
val _ = print_eval "handler_original_live"
  ``crep_to_loop$compile ^ctxt (insert 5 () LN)
      (crepLang$Call (SOME ([1],SOME (3w,crepLang$Skip))) «f»
         [crepLang$Const (1w : 8 word)])``;
