(* Full original native encoder theorem specialized only to Loc r c. *)
load "preamble"; load "riscv_targetProofTheory";
open HolKernel Parse bossLib preamble riscv_targetTheory riscv_targetProofTheory asmPropsTheory;
val _ = Globals.linewidth := 1000000;
val full = REWRITE_RULE [encoder_correct_def] riscv_encoder_correct;
val loc = GEN_ALL (Q.SPECL [`s1`, `Loc r c`, `s2`, `ms`] (CONJUNCT2 full));
val _ = (print "riscv_encoder_correct_loc_statement="; print_term (concl loc); print "\n");
val _ = print ("riscv_encoder_correct_loc_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string (type_of v)) (#1 (strip_forall (concl loc)))) ^ "\n");
val _ = print ("riscv_encoder_correct_loc_hypotheses=" ^ Int.toString (length (hyp loc)) ^ "\n");
val _ = (print "riscv_encoder_correct_loc_proved="; print_term (rhs (concl (EQT_INTRO loc))); print "\n");
val _ = OS.Process.exit OS.Process.success;
