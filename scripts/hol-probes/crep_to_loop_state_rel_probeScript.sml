(* Direct HOL observations for `crep_to_loopProofScript.sml` `state_rel_def`
   (lines 28-36) and `state_rel_intro` (lines 163-174).

   `state_rel` relates the 11-field `crepSem$state` to the 11-field
   `loopSem$state` on seven fields: memaddrs/mdomain, sh_memaddrs/sh_mdomain,
   clock, be, ffi, base_addr, top_addr.  The rows below build matching source
   and target states and perturb one field at a time.
*)
load "bossLib";
load "preamble";
load "crep_to_loopProofTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_to_loopProofTheory;

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
               memaddrs := ({} : 8 word set);
               sh_memaddrs := ({} : 8 word set);
               clock := 5;
               be := F;
               ffi := ARB;
               base_addr := 0w;
               top_addr := 100w |>) : (8, unit) crepSem$state``;

val t = ``(<| locals := (LN : 8 word_loc sptree$num_map);
               globals := (FEMPTY : 5 word |-> 8 word_loc);
               memory := K (Word (0w : 8 word));
               mdomain := ({} : 8 word set);
               sh_mdomain := ({} : 8 word set);
               clock := 5;
               code := (LN : (num list # 8 loopLang$prog) sptree$num_map);
               be := F;
               ffi := ARB;
               base_addr := 0w;
               top_addr := 100w |>) : (8, unit) loopSem$state``;

val _ = print_eval "memaddrs_mdomain_mem"
  ``(^s).memaddrs (8w : 8 word) = (^t).mdomain (8w : 8 word)``;
val _ = print_eval "sh_memaddrs_sh_mdomain_mem"
  ``(^s).sh_memaddrs (8w : 8 word) = (^t).sh_mdomain (8w : 8 word)``;
val _ = print_eval "clock_eq" ``(^s).clock = (^t).clock``;
val _ = print_eval "be_eq" ``(^s).be = (^t).be``;
val _ = print_eval "base_eq" ``(^s).base_addr = (^t).base_addr``;
val _ = print_eval "top_eq" ``(^s).top_addr = (^t).top_addr``;

val tBad = ``(<| locals := (LN : 8 word_loc sptree$num_map);
                 globals := (FEMPTY : 5 word |-> 8 word_loc);
                 memory := K (Word (0w : 8 word));
                 mdomain := ({} : 8 word set);
                 sh_mdomain := ({} : 8 word set);
                 clock := 6;
                 code := (LN : (num list # 8 loopLang$prog) sptree$num_map);
                 be := F;
                 ffi := ARB;
                 base_addr := 0w;
                 top_addr := 100w |>) : (8, unit) loopSem$state``;
val _ = print_eval "clock_mismatch" ``(^s).clock = (^tBad).clock``;
