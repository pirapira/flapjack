(* Direct HOL fixture for wordConvs$labels_rel.
   Reference: cakeml/compiler/backend/semantics/wordConvsScript.sml:139-143.

   `EVAL` alone leaves `set ... SUBSET set ...` unevaluated, so the fixture
   simplifies with `labels_rel_def` under `srw_ss()` (which knows
   `ALL_DISTINCT` and the finite-set membership rules) and prints the
   resulting `T`/`F`. *)
load "bossLib";
load "preamble";
load "wordConvsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordConvsTheory;

fun print_simp label q =
  let
    val th = SIMP_CONV (srw_ss()) [wordConvsTheory.labels_rel_def] q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val _ = print_simp "labels_rel_refl_ok"
  ``wordConvs$labels_rel ([1n;2] : num list) ([1n;2] : num list)``;
val _ = print_simp "labels_rel_subset_ok"
  ``wordConvs$labels_rel ([1n;2] : num list) ([1n] : num list)``;
val _ = print_simp "labels_rel_superset_bad"
  ``wordConvs$labels_rel ([1n] : num list) ([1n;2] : num list)``;
val _ = print_simp "labels_rel_dup_old_ok"
  ``wordConvs$labels_rel ([1n;1] : num list) ([1n] : num list)``;
val _ = print_simp "labels_rel_dup_new_bad"
  ``wordConvs$labels_rel ([1n;2] : num list) ([1n;1] : num list)``;
val _ = print_simp "labels_rel_empty_ok"
  ``wordConvs$labels_rel ([1n] : num list) ([] : num list)``;
val _ = print_simp "labels_rel_nil_bad"
  ``wordConvs$labels_rel ([] : num list) ([1n] : num list)``;
val _ = print_simp "labels_rel_append_concl_ok"
  ``wordConvs$labels_rel (([1n;2] ++ [3n]) : num list) (([1n] ++ []) : num list)``;
val _ = print_simp "labels_rel_pair_ok"
  ``wordConvs$labels_rel ([(1n,2); (3,4)] : (num # num) list)
      ([(1n,2)] : (num # num) list)``;