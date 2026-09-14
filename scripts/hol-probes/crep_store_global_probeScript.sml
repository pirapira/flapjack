(*
  Direct HOL observations for crepSem$evaluate's global store boundary.
  Reference: cakeml/pancake/semantics/crepSemScript.sml:61-63
  (set_globals_def) and :288-291 (evaluate StoreGlob).  The globals map is
  keyed at `5 word` while the stored values keep the target width, exactly as
  in the source `globals : 5 word |-> 'a word_lab`.
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

val store_state =
  ``(^s with <| locals := FEMPTY;
                 memory := (^s).memory;
                 memaddrs := {};
                 globals := FEMPTY |+ (4w, Word (11w:8 word));
                 base_addr := 12w;
                 top_addr := 13w |>)``;

val _ = print_eval "store_global_insert"
  ``case crepSem$evaluate
      (crepLang$StoreGlob (4w:5 word) (crepLang$Const (11w:8 word)),
       ^store_state with globals := FEMPTY) of
      | (res,s') => (res, FLOOKUP s'.globals (4w:5 word))``;

val _ = print_eval "store_global_update_sibling"
  ``case crepSem$evaluate
      (crepLang$StoreGlob (4w:5 word) (crepLang$Const (22w:8 word)),
       ^store_state with globals :=
         (FEMPTY |+ (4w, Word (11w:8 word))) |+ (8w, Word (9w:8 word))) of
      | (res,s') =>
          (res, FLOOKUP s'.globals (4w:5 word), FLOOKUP s'.globals (8w:5 word))``;

val _ = print_eval "store_global_eval_failure"
  ``case crepSem$evaluate
      (crepLang$StoreGlob (4w:5 word)
        (crepLang$Load (crepLang$Const (8w:8 word))), ^store_state) of
      | (res,s') => (res, FLOOKUP s'.globals (4w:5 word))``;

val _ = print_eval "store_global_then_load"
  ``case crepSem$evaluate
      (crepLang$StoreGlob (4w:5 word) (crepLang$Const (11w:8 word)),
       ^store_state with globals := FEMPTY) of
      | (res,s') => (res, crepSem$eval s' (crepLang$LoadGlob (4w:5 word)))``;
