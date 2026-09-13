(*
  Probe outputs for the original CakeML Pancake loopSem definition find_code.
  This is intentionally a HOL script rather than a second implementation.
  The checked-in output is regenerated with scripts/hol-probes/regenerate.sh.

  Reference: cakeml/pancake/semantics/loopSemScript.sml:147-163 (find_code_def).

  find_code has two clauses: SOME label looks the label up directly, while NONE
  expects the trailing argument to be a link (Loc loc 0) and binds the FRONT of
  the argument list to the code parameters, requiring
  LENGTH args = LENGTH params + 1.  Results are observed through sptree lookups
  of the returned parameter map (built by fromAList (ZIP (params, args))).
*)
load "bossLib";
load "preamble";
load "../semantics/loopSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open loopSemTheory;

val code2 = ``insert 5 (([1;2]:num list), loopLang$Skip) LN``;
val code1 = ``insert 9 (([7]:num list), loopLang$Skip) LN``;
val codeDup = ``insert 5 (([1;1]:num list), loopLang$Skip) LN``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "find_code_label_first"
  ``sptree$lookup 1 (FST (THE (loopSem$find_code (SOME 5) [Word 3w; Word 4w] ^code2)))``
val _ = print_eval "find_code_label_second"
  ``sptree$lookup 2 (FST (THE (loopSem$find_code (SOME 5) [Word 3w; Word 4w] ^code2)))``
val _ = print_eval "find_code_label_len_mismatch"
  ``loopSem$find_code (SOME 5) [Word 3w] ^code2``
val _ = print_eval "find_code_label_missing"
  ``loopSem$find_code (SOME 6) [Word 3w; Word 4w] ^code2``
val _ = print_eval "find_code_link_first"
  ``sptree$lookup 7 (FST (THE (loopSem$find_code NONE [Word 3w; wordLang$Loc 9 0] ^code1)))``
val _ = print_eval "find_code_link_wrong_len"
  ``loopSem$find_code NONE [wordLang$Loc 9 0] ^code1``
val _ = print_eval "find_code_empty_args"
  ``loopSem$find_code NONE [] ^code1``
val _ = print_eval "find_code_bad_last"
  ``loopSem$find_code NONE [Word 3w; Word 4w] ^code1``
val _ = print_eval "find_code_dup_first"
  ``sptree$lookup 1 (FST (THE (loopSem$find_code (SOME 5) [Word 5w; Word 7w] ^codeDup)))``
