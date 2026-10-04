val _ = loadPath := (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/step") ::
  (Globals.HOLDIR ^ "/examples/l3-machine-code/riscv/model") :: !loadPath;
load "riscv_stepTheory";
open HolKernel boolLib bossLib riscvTheory riscv_stepTheory;
val _ = Globals.linewidth := 1000000;
val slti_full = GEN_ALL (DISCH_ALL SLTI);
val _ = (print "slti_statement="; print_term(concl slti_full); print "\n");
val _ = print ("slti_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (#1(strip_forall(concl slti_full)))) ^ "\n");
val _ = print ("slti_source_hypotheses=" ^ Int.toString(length(hyp SLTI)) ^ "\n");
val _ = (print "slti_proved="; print_term(rhs(concl(EQT_INTRO slti_full))); print "\n");
val sltiu_full = GEN_ALL (DISCH_ALL SLTIU);
val _ = (print "sltiu_statement="; print_term(concl sltiu_full); print "\n");
val _ = print ("sltiu_types=" ^ String.concatWith ", " (map (fn v => term_to_string v ^ " : " ^ type_to_string(type_of v)) (#1(strip_forall(concl sltiu_full)))) ^ "\n");
val _ = print ("sltiu_source_hypotheses=" ^ Int.toString(length(hyp SLTIU)) ^ "\n");
val _ = (print "sltiu_proved="; print_term(rhs(concl(EQT_INTRO sltiu_full))); print "\n");
val _ = OS.Process.exit OS.Process.success;
