(*
  Direct HOL oracle for the CakeML backend `wordConvs` instruction predicates
  `distinct_tar_reg`, `two_reg_inst`, and `every_inst`.

  `distinct_tar_reg` checks that an instruction's destination differs from the
  registers it reads (for the arithmetic forms where that matters);
  `two_reg_inst` checks the destination equals the first source for the
  arithmetic forms that must be two-register; `every_inst` lifts an
  instruction predicate through `Seq`, `Loop`, `If`, `MustTerminate`, `Call`
  bodies, and the synthetic instruction of `OpCurrHeap` -- with the HOL
  nesting that `Call` returns `T` whenever the return metadata is `NONE`.

  Reference: cakeml/compiler/backend/semantics/wordConvsScript.sml:267-315.
*)
load "bossLib";
load "preamble";
load "wordConvsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordConvsTheory;
open wordLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val P = ``(\(i : 8 asm$inst). i = (asm$Skip : 8 asm$inst))``;

val instSkip = ``wordLang$Inst (asm$Skip : 8 asm$inst) :
  8 wordLang$prog``;
val instConst = ``wordLang$Inst (asm$Const 1 (0w:8 word)) :
  8 wordLang$prog``;
val opCurrHeap = ``wordLang$OpCurrHeap asm$Add 1 2 : 8 wordLang$prog``;
val callHandlerBad = ``wordLang$Call NONE NONE []
  (SOME (2, wordLang$Inst (asm$Const 1 (0w:8 word)), 20, 21)) :
  8 wordLang$prog``;
val callRetBad = ``wordLang$Call
  (SOME ([1], (sptree$LN : num_set, sptree$LN : num_set),
    wordLang$Inst (asm$Skip : 8 asm$inst), 10, 11))
  NONE [] (SOME (2, wordLang$Inst (asm$Const 1 (0w:8 word)), 20, 21)) :
  8 wordLang$prog``;
val callRetOk = ``wordLang$Call
  (SOME ([1], (sptree$LN : num_set, sptree$LN : num_set),
    wordLang$Inst (asm$Skip : 8 asm$inst), 10, 11)) NONE [] NONE :
  8 wordLang$prog``;
val loopOk = ``wordLang$Loop (sptree$LN : num_set)
  (wordLang$Inst (asm$Skip : 8 asm$inst)) (sptree$LN : num_set) :
  8 wordLang$prog``;
val allocProg = ``wordLang$Alloc 0
  ((sptree$LN : num_set, sptree$LN : num_set)) : 8 wordLang$prog``;

val () = print_eval "dtr_binop_same"
  ``distinct_tar_reg (asm$Arith (asm$Binop asm$Add 1 2 (asm$Reg 1)))``;
val () = print_eval "dtr_binop_diff"
  ``distinct_tar_reg (asm$Arith (asm$Binop asm$Add 1 2 (asm$Reg 3)))``;
val () = print_eval "dtr_addcarry_same"
  ``distinct_tar_reg (asm$Arith (asm$AddCarry 1 2 1 4))``;
val () = print_eval "dtr_skip" ``distinct_tar_reg asm$Skip``;
val () = print_eval "tri_binop_same"
  ``two_reg_inst (asm$Arith (asm$Binop asm$Add 1 1 (asm$Reg 1)))``;
val () = print_eval "tri_binop_diff"
  ``two_reg_inst (asm$Arith (asm$Binop asm$Add 1 2 (asm$Reg 1)))``;
val () = print_eval "tri_skip" ``two_reg_inst asm$Skip``;
val () = print_eval "ei_inst_ok" ``every_inst ^P ^instSkip``;
val () = print_eval "ei_inst_bad" ``every_inst ^P ^instConst``;
val () = print_eval "ei_opcurrheap" ``every_inst ^P ^opCurrHeap``;
val () = print_eval "ei_call_none" ``every_inst ^P ^callHandlerBad``;
val () = print_eval "ei_call_ret_bad" ``every_inst ^P ^callRetBad``;
val () = print_eval "ei_call_ret_ok" ``every_inst ^P ^callRetOk``;
val () = print_eval "ei_loop_ok" ``every_inst ^P ^loopOk``;
val () = print_eval "ei_alloc" ``every_inst ^P ^allocProg``;