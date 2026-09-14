(*
  Direct HOL observations for panSem$evaluate's explicit-memory stores.
  Reference: cakeml/pancake/semantics/panSemScript.sml:300-390
  (mem_store_byte_def/mem_store_32_def/mem_store_def/mem_stores_def) and
  :589-608 (evaluate Store/Store32/StoreByte).
*)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val memory_state =
  ``((((ARB:((64),unit) panSem$state) with clock := 20) with be := F) with
      memory := (8w =+ panSem$Word 0x0807060504030201w)
        (λ_. panSem$Word 0w)) with
      memaddrs := {8w}``;

val _ = print_eval "evaluate_store_word_hit"
  ``case panSem$evaluate
      (panLang$Store (panLang$Const (8w:64 word))
        (panLang$Const (0x1122334455667788w:64 word)), ^memory_state) of
      | (NONE,s) => SOME (s.memory 8w, s.memory 16w, s.clock)
      | _ => NONE``;

val _ = print_eval "evaluate_store_word_domain_failure"
  ``FST (panSem$evaluate
      (panLang$Store (panLang$Const (16w:64 word))
        (panLang$Const (0x1122334455667788w:64 word)), ^memory_state))``;

val _ = print_eval "evaluate_store32_hit"
  ``case panSem$evaluate
      (panLang$Store32 (panLang$Const (8w:64 word))
        (panLang$Const (0x11223344w:64 word)), ^memory_state) of
      | (NONE,s) => SOME (s.memory 8w, s.memory 16w, s.clock)
      | _ => NONE``;

val _ = print_eval "evaluate_store32_unaligned"
  ``FST (panSem$evaluate
      (panLang$Store32 (panLang$Const (9w:64 word))
        (panLang$Const (0x11223344w:64 word)), ^memory_state))``;

val _ = print_eval "evaluate_store_byte_hit"
  ``case panSem$evaluate
      (panLang$StoreByte (panLang$Const (9w:64 word))
        (panLang$Const (0xaaw:64 word)), ^memory_state) of
      | (NONE,s) => SOME (s.memory 8w, s.memory 16w, s.clock)
      | _ => NONE``;

val _ = print_eval "evaluate_store_byte_domain_failure"
  ``FST (panSem$evaluate
      (panLang$StoreByte (panLang$Const (16w:64 word))
        (panLang$Const (0xaaw:64 word)), ^memory_state))``;
