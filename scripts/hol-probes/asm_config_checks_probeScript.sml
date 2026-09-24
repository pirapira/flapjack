load "bossLib";
load "preamble";
load "asmTheory";
load "stackPropsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open asmTheory;
open stackPropsTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val cfg = ``<| ISA := RISC_V
   ; encode := (\x. ([] : word8 list))
   ; big_endian := F
   ; code_alignment := 2
   ; link_reg := NONE
   ; avoid_regs := [3]
   ; reg_count := 8
   ; fp_reg_count := 4
   ; two_reg_arith := T
   ; valid_imm := (K (K T))
   ; addr_offset := (0w, 100w)
   ; hw_offset := (0w, 100w)
   ; byte_offset := (0w, 100w)
   ; jump_offset := (0w, 100w)
   ; cjump_offset := (0w, 100w)
   ; loc_offset := (0w, 100w)
   |> : 8 asm_config``;

val _ = print_eval "aligned0" ``alignment$aligned 0 (8w:8 word)``
val _ = print_eval "aligned2" ``alignment$aligned 2 (8w:8 word)``
val _ = print_eval "unaligned2" ``alignment$aligned 2 (10w:8 word)``
val _ = print_eval "regOk2" ``asm$reg_ok 2 ^cfg``
val _ = print_eval "regOk3" ``asm$reg_ok 3 ^cfg``
val _ = print_eval "regOk8" ``asm$reg_ok 8 ^cfg``
val _ = print_eval "fpRegOk3" ``asm$fp_reg_ok 3 ^cfg``
val _ = print_eval "fpRegOk4" ``asm$fp_reg_ok 4 ^cfg``
val _ = print_eval "regImmReg" ``asm$reg_imm_ok (INL asm$Add) (asm$Reg 2) ^cfg``
val _ = print_eval "regImmXorMinus1" ``asm$reg_imm_ok (INL asm$Xor) (asm$Imm (-1w:8 word)) ^cfg``
val _ = print_eval "regImmXorOther" ``asm$reg_imm_ok (INL asm$Xor) (asm$Imm (5w:8 word)) ^cfg``
val _ = print_eval "arithBinopOk"
  ``asm$arith_ok (asm$Binop asm$Add 2 2 (asm$Imm (1w:8 word))) ^cfg``
val _ = print_eval "arithBinopTwoRegBad"
  ``asm$arith_ok (asm$Binop asm$Add 2 1 (asm$Imm (1w:8 word))) ^cfg``
val _ = print_eval "arithShiftOk"
  ``asm$arith_ok (asm$Shift ast$Lsl 2 2 (asm$Imm (3w:8 word))) ^cfg``
val _ = print_eval "arithShiftWidth"
  ``asm$arith_ok (asm$Shift ast$Lsl 2 2 (asm$Imm (8w:8 word))) ^cfg``
val _ = print_eval "arithDivOk" ``asm$arith_ok (asm$Div 1 2 3) ^cfg``
val _ = print_eval "arithAddCarryOk" ``asm$arith_ok (asm$AddCarry 1 2 3 4) ^cfg``
val _ = print_eval "arithAddCarryBad" ``asm$arith_ok (asm$AddCarry 1 2 1 4) ^cfg``
val _ = print_eval "arithLongDivBad" ``asm$arith_ok (asm$LongDiv 0 2 2 0 3) ^cfg``
val _ = print_eval "fpLessOk" ``asm$fp_ok (asm$FPLess 1 2 3) ^cfg``
val _ = print_eval "fpFmaBad" ``asm$fp_ok (asm$FPFma 1 2 3) ^cfg``
val _ = print_eval "fpAbsTwoReg" ``asm$fp_ok (asm$FPAbs 2 2) ^cfg``
val _ = print_eval "cmpOk" ``asm$cmp_ok asm$Equal 2 (asm$Imm (1w:8 word)) ^cfg``
val _ = print_eval "addrOffsetOk" ``asm$offset_ok 0 (^cfg).addr_offset (8w:8 word)``
val _ = print_eval "hwOffsetOk" ``asm$offset_ok 0 (^cfg).hw_offset (8w:8 word)``
val _ = print_eval "byteOffsetOk" ``asm$offset_ok 0 (^cfg).byte_offset (101w:8 word)``
val _ = print_eval "jumpOffsetOk" ``asm$offset_ok (^cfg).code_alignment (^cfg).jump_offset (200w:8 word)``
val _ = print_eval "jumpOffsetUnaligned" ``asm$offset_ok (^cfg).code_alignment (^cfg).jump_offset (3w:8 word)``
val _ = print_eval "instConstOk" ``asm$inst_ok (asm$Const 2 (0w:8 word)) ^cfg``
val _ = print_eval "instArithOk" ``asm$inst_ok (asm$Arith (asm$Div 1 2 3)) ^cfg``
val _ = print_eval "instFpOk" ``asm$inst_ok (asm$FP (asm$FPLess 1 2 3)) ^cfg``
val _ = print_eval "instMemLoadOk"
  ``asm$inst_ok (asm$Mem asm$Load 2 (asm$Addr 2 (8w:8 word))) ^cfg``
val _ = print_eval "instMemHwOk"
  ``asm$inst_ok (asm$Mem asm$Load16 2 (asm$Addr 2 (8w:8 word))) ^cfg``
val _ = print_eval "instMemByteOk"
  ``asm$inst_ok (asm$Mem asm$Load8 2 (asm$Addr 2 (8w:8 word))) ^cfg``
val _ = print_eval "stackAddrLoad"
  ``stackProps$addr_ok asm$Load (asm$Addr 2 (8w:8 word)) ^cfg``
val _ = print_eval "stackAddrHw"
  ``stackProps$addr_ok asm$Load16 (asm$Addr 2 (8w:8 word)) ^cfg``
val _ = print_eval "stackAddrByte"
  ``stackProps$addr_ok asm$Store8 (asm$Addr 2 (8w:8 word)) ^cfg``
val _ = print_eval "signedHighLeZero" ``(128w:8 word) <= (0w:8 word)``
val _ = print_eval "unsignedHighLeZero" ``word_ls (128w:8 word) (0w:8 word)``
val _ = print_eval "signedOffsetBounds" ``asm$offset_ok 0 (0w,255w) (200w:8 word)``
val _ = print_eval "asmOkInstConst" ``asm$asm_ok (asm$Inst (asm$Const 2 (0w:8 word))) ^cfg``
val _ = print_eval "asmOkJump" ``asm$asm_ok (asm$Jump (100w:8 word)) ^cfg``
val _ = print_eval "asmOkJumpCmp"
  ``asm$asm_ok (asm$JumpCmp asm$Equal 1 (asm$Reg 2) (100w:8 word)) ^cfg``
val _ = print_eval "asmOkCallNone" ``asm$asm_ok (asm$Call (100w:8 word)) ^cfg``
val _ = print_eval "asmOkJumpReg" ``asm$asm_ok (asm$JumpReg 3) ^cfg``
val _ = print_eval "asmOkLoc" ``asm$asm_ok (asm$Loc 1 (100w:8 word)) ^cfg``