(*
  Direct HOL-EVAL probes for Pancake crepSem eval.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:90-166.
*)
load "bossLib";
load "preamble";
load "crepSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crepSemTheory;

val s = ``(s:(8,unit) crepSem$state)``;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val hit_state =
  ``^s with <| locals := FEMPTY |+ (1, Word (7w:8 word));
                memory := (3w =+ Word (9w:8 word)) (^s).memory;
                memaddrs := {3w};
                globals := FEMPTY |+ (4w, Word (11w:8 word));
                base_addr := 12w;
                top_addr := 13w |>``;

val _ = print_eval "eval_const"
  ``crepSem$eval ^hit_state (crepLang$Const (5w:8 word))``;
val _ = print_eval "eval_local_hit"
  ``crepSem$eval ^hit_state (crepLang$Var 1)``;
val _ = print_eval "eval_local_miss"
  ``crepSem$eval ^hit_state (crepLang$Var 2)``;
val _ = print_eval "eval_memory_hit"
  ``crepSem$eval ^hit_state (crepLang$Load (crepLang$Const (3w:8 word)))``;
val _ = print_eval "eval_memory_miss"
  ``crepSem$eval ^hit_state (crepLang$Load (crepLang$Const (8w:8 word)))``;
val _ = print_eval "eval_global_hit"
  ``crepSem$eval ^hit_state (crepLang$LoadGlob (4w:5 word))``;
val _ = print_eval "eval_global_miss"
  ``crepSem$eval ^hit_state (crepLang$LoadGlob (8w:5 word))``;
val _ = print_eval "eval_base_top"
  ``(crepSem$eval ^hit_state crepLang$BaseAddr,
     crepSem$eval ^hit_state crepLang$TopAddr)``;
