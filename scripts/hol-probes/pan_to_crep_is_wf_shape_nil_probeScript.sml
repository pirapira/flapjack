(* The pan_to_crep is_wf_shape_nil_length_flatten probe observes the exact
   flatten/size_of_shape relationship under the empty constructor context
   (pan_to_crepProofScript.sml:2469). *)
load "bossLib";
load "preamble";
load "panLangTheory";
load "panSemTheory";

open bossLib;
open HolKernel Parse;
open preamble;
open panLangTheory;
open panSemTheory;

fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "iwf_val"
  ``LENGTH (flatten (ValWord (5w : 64 word))) =
    size_of_shape (shape_of (ValWord (5w : 64 word)))``;

val _ = print_eval "iwf_struct"
  ``LENGTH (flatten (RStruct [ValWord (1w : 64 word); ValWord (2w : 64 word)])) =
    size_of_shape (shape_of (RStruct [ValWord (1w : 64 word); ValWord (2w : 64 word)]))``;

val _ = print_eval "iwf_nested"
  ``LENGTH (flatten (RStruct [RStruct [ValWord (1w : 64 word)]; ValWord (2w : 64 word)])) =
    size_of_shape (shape_of (RStruct [RStruct [ValWord (1w : 64 word)]; ValWord (2w : 64 word)]))``;

val _ = print_eval "iwf_val_len"
  ``LENGTH (flatten (ValWord (5w : 64 word)))``;

val _ = print_eval "iwf_size_val"
  ``size_of_shape (shape_of (ValWord (5w : 64 word)))``;

val _ = print_eval "iwf_wf_val"
  ``is_wf_shape ([] : (stcname # struct_info) list) (shape_of (ValWord (5w : 64 word)))``;

val _ = print_eval "iwf_wf_struct"
  ``is_wf_shape ([] : (stcname # struct_info) list)
    (shape_of (RStruct [ValWord (1w : 64 word); ValWord (2w : 64 word)]))``;
