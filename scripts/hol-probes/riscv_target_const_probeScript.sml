(* Full original native encoder theorem specialized only to Inst (Const r c). *)
load "preamble"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory riscv_targetProofTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val full = REWRITE_RULE [encoder_correct_def] riscv_encoder_correct;
val const = GEN_ALL (Q.SPECL [`s1`, `Inst (Const r c)`, `s2`, `ms`] (CONJUNCT2 full));
val _ = (print "riscv_encoder_correct_const_statement="; print_term (concl const); print "\n");
val _ = print ("riscv_encoder_correct_const_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl const)))) ^ "\n");
val _ = print ("riscv_encoder_correct_const_hypotheses=" ^ Int.toString (length (hyp const)) ^ "\n");
val _ = (print "riscv_encoder_correct_const_proved="; print_term (rhs (concl (EQT_INTRO const))); print "\n");
val _ = OS.Process.exit OS.Process.success;
