(* Direct HOL-EVAL observations for `cont_res` (`crep_inlineProofScript.sml:2168`),
   the finite-result predicate used by `transform_branch_correct` /
   `inline_prog_correct`.  Each row is a boolean equality so it prints on one
   line; the Lean counterpart is `Flapjack.contResHOL`.

   References:
     cakeml/pancake/proofs/crep_inlineProofScript.sml:2168-2171: cont_res_def *)

load "bossLib";
load "preamble";
load "crep_inlineProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_eval "cont_res_none"
  ``(cont_res (NONE : 8 crepSem$result option) = T)``;
val _ = print_eval "cont_res_break"
  ``(cont_res (SOME (Break 3)) = T)``;
val _ = print_eval "cont_res_continue"
  ``(cont_res (SOME (Continue 2)) = T)``;
val _ = print_eval "cont_res_error"
  ``(cont_res (SOME Error) = T)``;
val _ = print_eval "cont_res_normal"
  ``(cont_res (SOME (Return ([] : (8 word_lab) list))) = F)``;
val _ = print_eval "cont_res_timeout"
  ``(cont_res (SOME TimeOut) = F)``;
val _ = print_eval "cont_res_done" ``0``;