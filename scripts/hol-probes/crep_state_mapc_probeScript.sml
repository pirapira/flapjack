(* Direct HOL evaluation of FMAP_MAP2 as used by the local mapc overload in
   crep_arithProofScript.sml:109. *)
load "bossLib";
load "finite_mapTheory";
open bossLib;
open HolKernel Parse;
open finite_mapTheory;

val map2_lookup_thm = Q.prove(
  `FLOOKUP
      (FMAP_MAP2 (\(key, value). value + 1)
        (FEMPTY |+ (3:num, 7:num))) 3 = SOME 8`,
  simp [FLOOKUP_FMAP_MAP2, FLOOKUP_UPDATE]);
val _ = (print "fmap_map2_keyed_lookup=T\n"; map2_lookup_thm);
