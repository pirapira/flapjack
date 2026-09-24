(* Direct HOL-EVAL observations for `crepProps$dec_clock_simp` and
   `crepProps$empty_locals_simp`.

   Reference:
     cakeml/pancake/semantics/crepPropsScript.sml:267 (dec_clock_simp)
     cakeml/pancake/semantics/crepPropsScript.sml:282 (empty_locals_simp)

   The two HOL theorems are 10-conjunct projection equalities over the
   11-field `crepSem$state`.  Each row below observes one representative
   component after `dec_clock`/`empty_locals`, pinning the changed field and
   several unchanged fields on a concrete state.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
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

val s = ``(<| locals := FEMPTY;
               globals := FEMPTY;
               code := FEMPTY;
               memory := K (Word (0w : 8 word));
               memaddrs := {};
               sh_memaddrs := {};
               clock := 5;
               be := F;
               ffi := ARB;
               base_addr := 0w;
               top_addr := 100w |>) : (8, unit) crepSem$state``;

val _ = print_eval "dec_clock_clock" ``(dec_clock ^s).clock = 4``;
val _ = print_eval "dec_clock_globals"
  ``FLOOKUP (dec_clock ^s).globals (0w : 5 word) =
      FLOOKUP (^s).globals (0w : 5 word)``;
val _ = print_eval "dec_clock_be" ``(dec_clock ^s).be = F``;
val _ = print_eval "dec_clock_top" ``(dec_clock ^s).top_addr = 100w``;
val _ = print_eval "empty_locals_locals"
  ``FLOOKUP (empty_locals ^s).locals (0 : num) = NONE``;
val _ = print_eval "empty_locals_clock" ``(empty_locals ^s).clock = 5``;
val _ = print_eval "empty_locals_memory"
  ``(empty_locals ^s).memory (8w : 8 word) = Word 0w``;
