(* Direct HOL-EVAL observations for CakeML total_colour and setup_ssa.
   References: word_allocScript.sml:1592-1599, 1809-1814. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_allocTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val colour = ``sptree$fromAList [(1n,7n); (3n,9n)]``;
val _ = print_eval "total_colour_mapped_1"
  ``total_colour ^colour 1``;
val _ = print_eval "total_colour_mapped_3"
  ``total_colour ^colour 3``;
val _ = print_eval "total_colour_physical_2"
  ``total_colour ^colour 2``;
val _ = print_eval "total_colour_unmapped_5"
  ``total_colour ^colour 5``;

val setup3 = ``setup_ssa 3 5 (Skip : num wordLang$prog)``;
val _ = print_eval "setup3_move" ``FST (^setup3)``;
val _ = print_eval "setup3_ssa" ``sptree$toAList (FST (SND (^setup3)))``;
val _ = print_eval "setup3_next" ``SND (SND (^setup3))``;

val setup0 = ``setup_ssa 0 9 (Skip : num wordLang$prog)``;
val _ = print_eval "setup0_move" ``FST (^setup0)``;
val _ = print_eval "setup0_ssa" ``sptree$toAList (FST (SND (^setup0)))``;
val _ = print_eval "setup0_next" ``SND (SND (^setup0))``;
