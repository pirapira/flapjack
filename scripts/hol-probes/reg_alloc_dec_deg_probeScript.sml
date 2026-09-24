(* Direct HOL-EVAL boundary observations for reg_alloc$dec_deg.
   References: reg_allocScript.sml:252-257 and
   reg_allocProofScript.sml:160-168, 229-237. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open reg_allocTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end;

val state =
  ``<| adj_ls := []; node_tag := []; degrees := [3]; dim := 1;
       simp_wl := []; spill_wl := []; freeze_wl := [];
       avail_moves_wl := []; unavail_moves_wl := [];
       coalesced := []; move_related := []; stack := [] |>``;

val _ = print_eval "dec_deg_in_bounds_result"
  ``FST (dec_deg 0 ^state)``;
val _ = print_eval "dec_deg_in_bounds_degrees"
  ``(SND (dec_deg 0 ^state)).degrees``;
val _ = print_eval "dec_deg_out_of_bounds_result"
  ``FST (dec_deg 1 ^state)``;
val _ = print_eval "dec_deg_out_of_bounds_state_unchanged"
  ``SND (dec_deg 1 ^state) = ^state``;
val _ = print_eval "degrees_sub_out_of_bounds_result"
  ``FST (degrees_sub 1 ^state)``;
val _ = print_eval "update_degrees_out_of_bounds_result"
  ``FST (update_degrees 1 8 ^state)``;
