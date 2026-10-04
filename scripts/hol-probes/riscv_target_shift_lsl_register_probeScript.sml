(* Full original native encoder theorem specialized only to Inst (Arith (Shift Lsl rd rs1 (Reg rs2))). *)
load "preamble"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory riscv_targetProofTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val full = REWRITE_RULE [encoder_correct_def] riscv_encoder_correct;
val shift_case = GEN_ALL (Q.SPECL [`s1`, `Inst (Arith (Shift Lsl rd rs1 (Reg rs2)))`, `s2`, `ms`] (CONJUNCT2 full));
val _ = (print "riscv_encoder_correct_shiftLslRegister_statement="; print_term (concl shift_case); print "\n");
val _ = print ("riscv_encoder_correct_shiftLslRegister_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl shift_case)))) ^ "\n");
val _ = print ("riscv_encoder_correct_shiftLslRegister_hypotheses=" ^ Int.toString (length (hyp shift_case)) ^ "\n");
val _ = (print "riscv_encoder_correct_shiftLslRegister_proved="; print_term (rhs (concl (EQT_INTRO shift_case))); print "\n");
val _ = OS.Process.exit OS.Process.success;
