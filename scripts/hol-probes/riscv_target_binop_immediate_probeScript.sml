(* Full original native encoder theorem specialized only to Inst (Arith (Binop bop rd rs1 (Imm immv))). *)
load "preamble"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory riscv_targetProofTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val full = REWRITE_RULE [encoder_correct_def] riscv_encoder_correct;
val binop = GEN_ALL (Q.SPECL [`s1`, `Inst (Arith (Binop bop rd rs1 (Imm immv)))`, `s2`, `ms`] (CONJUNCT2 full));
val _ = (print "riscv_encoder_correct_binop_immediate_statement="; print_term (concl binop); print "\n");
val _ = print ("riscv_encoder_correct_binop_immediate_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl binop)))) ^ "\n");
val _ = print ("riscv_encoder_correct_binop_immediate_hypotheses=" ^ Int.toString (length (hyp binop)) ^ "\n");
val _ = (print "riscv_encoder_correct_binop_immediate_proved="; print_term (rhs (concl (EQT_INTRO binop))); print "\n");
val _ = OS.Process.exit OS.Process.success;
