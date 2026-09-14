(* Direct HOL-EVAL fixture for word_alloc$get_forced on RISC-V.
   Reference: cakeml/compiler/backend/word_allocScript.sml:1466. *)
load "bossLib";
load "preamble";
val _ = loadPath := "../cv_compute/.hol/objs" :: !loadPath;
val _ = load "backend_riscvTheory";
load "word_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end

val cfg = ``riscv_config``;

val _ = print_eval "gf_longmul"
  ``word_alloc$get_forced ^cfg
      (wordLang$Inst (Arith (LongMul 9 11 13 17))) []``;
val _ = print_eval "gf_longmul_eq"
  ``word_alloc$get_forced ^cfg
      (wordLang$Inst (Arith (LongMul 9 11 9 17))) []``;
val _ = print_eval "gf_addcarry"
  ``word_alloc$get_forced ^cfg
      (wordLang$Inst (Arith (AddCarry 9 11 13 17))) []``;
val _ = print_eval "gf_addcarry_eq4"
  ``word_alloc$get_forced ^cfg
      (wordLang$Inst (Arith (AddCarry 9 11 13 9))) []``;
val _ = print_eval "gf_seq"
  ``word_alloc$get_forced ^cfg
      (wordLang$Seq (wordLang$Inst (Arith (LongMul 9 11 13 17)))
                    (wordLang$Inst (Arith (AddCarry 21 2 25 29)))) []``;
val _ = print_eval "gf_if"
  ``word_alloc$get_forced ^cfg
      (wordLang$If NotEqual 2 (Reg 3)
         (wordLang$Inst (Arith (LongMul 9 11 13 17)))
         (wordLang$Inst (Arith (AddCarry 21 2 25 29)))) []``;
val _ = print_eval "gf_call"
  ``word_alloc$get_forced ^cfg
      (wordLang$Call (SOME ([],(LN,LN),wordLang$Inst (Arith (LongMul 9 11 13 17)),0,1))
         (SOME 5) [2] NONE) []``;
val _ = print_eval "gf_call_handler"
  ``word_alloc$get_forced ^cfg
      (wordLang$Call (SOME ([],(LN,LN),wordLang$Inst (Arith (LongMul 9 11 13 17)),0,1))
         (SOME 5) [2]
         (SOME (11,wordLang$Inst (Arith (AddCarry 21 2 25 29)),0,2))) []``;
val _ = print_eval "gf_loop"
  ``word_alloc$get_forced ^cfg
      (wordLang$Loop LN (wordLang$Inst (Arith (LongMul 9 11 13 17))) LN) []``;
(* The catch-all clause (no forcing for other Arith/Mem/Set/FP shapes) is
   covered by the Lean guards over the port's fall-through case. *)
