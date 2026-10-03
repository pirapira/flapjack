load "preamble"; load "riscv_targetTheory";
open HolKernel Parse bossLib preamble riscvTheory riscv_targetTheory asmTheory;
val _ = Globals.linewidth := 1000000;
val _ = computeLib.add_funs [Run_def,gpr_def,GPR_def,write'gpr_def,write'GPR_def,
 dfn'ORI_def,dfn'LUI_def,dfn'ADDI_def,dfn'XORI_def,dfn'SLLI_def,
 dfn'OR_def,dfn'XOR_def,in32BitMode_def,curArch_def,architecture_def,MCSR_def];
fun out label tm = let
 val th = (EVAL THENC SIMP_CONV (srw_ss()) [riscv_state_fn_updates] THENC EVAL) tm
 val result = rhs(concl th)
 in if null(hyp th) andalso aconv result ``T`` then
   (print(label ^ "="); print_term result; print "\n")
 else raise Fail ("non-true original Run observation: " ^ label) end;
val _ = out "const_run_small_zero" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (0w:word64))))
 in (GPR 5w r = 0w /\ GPR 31w r = 99w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = out "const_run_small_positive" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (2047w:word64))))
 in (GPR 5w r = 2047w /\ GPR 31w r = 99w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = out "const_run_small_negative" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (18446744073709549568w:word64))))
 in (GPR 5w r = 18446744073709549568w /\ GPR 31w r = 99w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = out "const_run_small_all_ones" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (18446744073709551615w:word64))))
 in (GPR 5w r = 18446744073709551615w /\ GPR 31w r = 99w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = out "const_run_medium_positive" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (2048w:word64))))
 in (GPR 5w r = 2048w /\ GPR 31w r = 99w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = out "const_run_medium_positive_max" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (2147483647w:word64))))
 in (GPR 5w r = 2147483647w /\ GPR 31w r = 99w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = out "const_run_medium_negative" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (18446744071562067968w:word64))))
 in (GPR 5w r = 18446744071562067968w /\ GPR 31w r = 99w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = out "const_run_medium_negative_low11" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (18446744071562070016w:word64))))
 in (GPR 5w r = 18446744071562070016w /\ GPR 31w r = 99w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = out "const_run_wide_or" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (4294967297w:word64))))
 in (GPR 5w r = 4294967297w /\ GPR 31w r = 1w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = out "const_run_wide_or_high11" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (8796093024255w:word64))))
 in (GPR 5w r = 8796093024255w /\ GPR 31w r = 2047w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = out "const_run_wide_xor" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (6442450944w:word64))))
 in (GPR 5w r = 6442450944w /\ GPR 31w r = 18446744071562067968w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = out "const_run_wide_xor_low11_high11" ``let
 s = (ARB:riscv_state) with <|procID := 0w;
     c_gpr := (\core reg. 99w);
     c_MCSR := (\core. (ARB:MachineCSR) with
       mcpuid := ((ARB:mcpuid) with ArchBase := 2w))|>;
 r = FOLDL (\s i. riscv$Run i s) s (riscv_ast (Inst (Const 5 (8798240507904w:word64))))
 in (GPR 5w r = 8798240507904w /\ GPR 31w r = 18446744071562070016w /\
     GPR 6w r = 99w /\ r.c_gpr 1w 5w = 99w /\ r.c_gpr 0w 0w = 99w /\
     (r with c_gpr := s.c_gpr) = s)``;
val _ = OS.Process.exit OS.Process.success;
