load "preamble"; load "riscv_stepTheory";
open HolKernel Parse bossLib preamble riscvTheory riscv_stepTheory;
val _ = computeLib.add_funs [Encode_def, Utype_def, Itype_def, Rtype_def, opc_def];
val _ = Globals.linewidth := 1000000;
val _ = (print "const_next_wrapper_type="; print_type(type_of ``riscv_step$NextRISCV``); print "\n");
val _ = (print "const_next_fetch_type="; print_type(type_of ``riscv_step$Fetch``); print "\n");
fun out label tm = let val th = EVAL tm val r = rhs(concl th) in
 if null(hyp th) andalso aconv r ``T`` then
 (print(label ^ "="); print_term r; print "\n")
 else raise Fail ("nontrue native instruction width: " ^ label) end;
val _ = out "const_next_lui_zero" ``((Encode (ArithI (LUI (5w,0w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_lui_all_ones" ``((Encode (ArithI (LUI (5w,1048575w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_addi_zero" ``((Encode (ArithI (ADDI (5w,6w,0w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_addi_all_ones" ``((Encode (ArithI (ADDI (5w,6w,4095w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_ori_zero" ``((Encode (ArithI (ORI (5w,6w,0w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_ori_all_ones" ``((Encode (ArithI (ORI (5w,6w,4095w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_xori_zero" ``((Encode (ArithI (XORI (5w,6w,0w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_xori_all_ones" ``((Encode (ArithI (XORI (5w,6w,4095w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_slli_zero" ``((Encode (Shift (SLLI (5w,6w,0w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_slli_all_ones" ``((Encode (Shift (SLLI (5w,6w,63w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_or_zero" ``((Encode (ArithR (OR (5w,6w,0w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_or_all_ones" ``((Encode (ArithR (OR (5w,6w,31w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_xor_zero" ``((Encode (ArithR (XOR (5w,6w,0w)))) && (3w:word32)) = 3w``;
val _ = out "const_next_xor_all_ones" ``((Encode (ArithR (XOR (5w,6w,31w)))) && (3w:word32)) = 3w``;
val _ = OS.Process.exit OS.Process.success;
