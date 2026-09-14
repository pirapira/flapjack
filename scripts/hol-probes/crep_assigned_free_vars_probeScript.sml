(* Direct HOL-EVAL probes for crepLang$assigned_free_vars.
   Reference: cakeml/pancake/crepLangScript.sml:149-162. *)
load "bossLib";
load "preamble";
load "../crepLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "skip"
  ``crepLang$assigned_free_vars (Skip : 8 crepLang$prog)``;
val _ = print_eval "assign"
  ``crepLang$assigned_free_vars
      (Assign 7 (Const (3w : 8 word)) : 8 crepLang$prog)``;
val _ = print_eval "dec_filter"
  ``crepLang$assigned_free_vars
      (Dec 2 (Const (3w : 8 word))
        (Seq (Assign 2 (Const (4w : 8 word)))
          (Assign 5 (Const (6w : 8 word)))) : 8 crepLang$prog)``;
val _ = print_eval "seq"
  ``crepLang$assigned_free_vars
      (Seq (Assign 1 (Const (3w : 8 word)))
        (Assign 4 (Const (6w : 8 word))) : 8 crepLang$prog)``;
val _ = print_eval "if_while"
  ``(crepLang$assigned_free_vars
      (If (Const (1w : 8 word))
        (Assign 1 (Const (3w : 8 word)))
        (Assign 4 (Const (6w : 8 word))) : 8 crepLang$prog),
     crepLang$assigned_free_vars
      (While (Const (1w : 8 word))
        (Assign 6 (Const (8w : 8 word))) : 8 crepLang$prog))``;
val _ = print_eval "shmem_fallback"
  ``(crepLang$assigned_free_vars
      (ShMem Load 9 (Const (0w : 8 word)) : 8 crepLang$prog),
     crepLang$assigned_free_vars
      (Store (Const (0w : 8 word)) (Const (1w : 8 word)) : 8 crepLang$prog))``;
