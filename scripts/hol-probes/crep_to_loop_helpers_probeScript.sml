(* Direct HOL observations for the pure-num helper definitions of
   `crep_to_loopScript.sml`:
     gen_temps_def (line 101): gen_temps n l = GENLIST (\x. n + x) l
     rt_var_def    (line 105): resolve a return variable, sentinel mx+1
     rt_vars_def   (line 113): OPT_MMAP FLOOKUP resolver, sentinel [mx+1]
     first_name_def(line 243): first_name = 64
   These definitions carry no word-typed fields; the rows below evaluate them on
   concrete inputs.
*)
load "bossLib";
load "preamble";
load "crep_to_loopTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open finite_mapTheory;
open crep_to_loopTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val fm = ``((FEMPTY |+ ((1:num), (10:num)) |+ ((2:num), (7:num)))
            : (num, num) fmap)``;

val _ = print_eval "gen_temps_3" ``gen_temps (5:num) (3:num)``;
val _ = print_eval "first_name" ``first_name : num``;
val _ = print_eval "rt_var_some" ``rt_var ^fm (SOME (2:num)) (9:num) (99:num)``;
val _ = print_eval "rt_var_none" ``rt_var ^fm NONE (9:num) (99:num)``;
val _ = print_eval "rt_var_absent" ``rt_var ^fm (SOME (4:num)) (9:num) (99:num)``;
val _ = print_eval "rt_vars_some" ``rt_vars ^fm [(1:num); (2:num)] (99:num)``;
val _ = print_eval "rt_vars_absent" ``rt_vars ^fm [(1:num); (4:num)] (99:num)``;
