(* Direct-HOL oracle for panPropsScript.sml:171 length_flatten_eq_size_of_shape.
   Observes LENGTH (flatten v) and size_of_shape (shape_of v) for the exact
   panSem values, plus the empty-context well-formedness hypothesis. *)

load "bossLib";
load "preamble";
load "panSemTheory";
load "panPropsTheory";

open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;
open panPropsTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "lfs_val"
  ``(LENGTH (flatten (ValWord (5w : 64 word))) =
     size_of_shape (shape_of (ValWord (5w : 64 word))))``;

val _ = print_eval "lfs_two"
  ``(LENGTH (flatten (RStruct [ValWord (1w : 64 word); ValWord (2w : 64 word)])) =
     size_of_shape (shape_of (RStruct [ValWord (1w : 64 word); ValWord (2w : 64 word)])))``;

val _ = print_eval "lfs_nested"
  ``(LENGTH (flatten (RStruct [RStruct [ValWord (1w : 64 word)]; ValWord (2w : 64 word)])) =
     size_of_shape (shape_of (RStruct [RStruct [ValWord (1w : 64 word)]; ValWord (2w : 64 word)])))``;

val _ = print_eval "lfs_val_len"
  ``LENGTH (flatten (ValWord (5w : 64 word)))``;

val _ = print_eval "lfs_nested_len"
  ``LENGTH (flatten (RStruct [RStruct [ValWord (1w : 64 word)]; ValWord (2w : 64 word)]))``;

val _ = print_eval "lfs_wf_nested"
  ``is_wf_shape [] (shape_of (RStruct [RStruct [ValWord (1w : 64 word)]; ValWord (2w : 64 word)]))``;
