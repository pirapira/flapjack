(* Full original native encoder theorem specialized only to Inst (Arith (Div rd rs1 rs2)). *)
load "preamble"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory riscv_targetProofTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val full = REWRITE_RULE [encoder_correct_def] riscv_encoder_correct;
val div_case = GEN_ALL (Q.SPECL [`s1`, `Inst (Arith (Div rd rs1 rs2))`, `s2`, `ms`] (CONJUNCT2 full));
val _ = (print "riscv_encoder_correct_div_statement="; print_term (concl div_case); print "\n");
val _ = print ("riscv_encoder_correct_div_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl div_case)))) ^ "\n");
val _ = print ("riscv_encoder_correct_div_hypotheses=" ^ Int.toString (length (hyp div_case)) ^ "\n");
val _ = (print "riscv_encoder_correct_div_proved="; print_term (rhs (concl (EQT_INTRO div_case))); print "\n");
val _ = OS.Process.exit OS.Process.success;
