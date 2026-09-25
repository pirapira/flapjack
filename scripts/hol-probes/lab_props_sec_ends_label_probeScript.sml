load "preamble";
load "labPropsTheory";
open bossLib; open HolKernel Parse; open preamble;
open labSemTheory; open labPropsTheory; open labLangTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val lbl = ``(labLang$Label 0 1 0 : 8 labLang$line)``;
val asmLine = ``(labLang$Asm (labLang$Asmi (asm$Inst asm$Skip)) [] 0 : 8 labLang$line)``;
val secLabel = ``(labLang$Section 0 [^lbl] : 8 labLang$sec)``;
val secAsm = ``(labLang$Section 0 [^asmLine] : 8 labLang$sec)``;
val secEmpty = ``(labLang$Section 0 [] : 8 labLang$sec)``;

val _ = print_eval "is_label_label" ``labSem$is_Label ^lbl``;
val _ = print_eval "is_label_asm" ``labSem$is_Label ^asmLine``;
val _ = print_eval "sec_label_end" ``labProps$sec_ends_with_label ^secLabel``;
val _ = print_eval "sec_asm_end" ``labProps$sec_ends_with_label ^secAsm``;
val _ = print_eval "sec_empty" ``labProps$sec_ends_with_label ^secEmpty``;