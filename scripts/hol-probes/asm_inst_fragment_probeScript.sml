load "bossLib";
load "preamble";
load "asmTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL over the assembly payload carriers that back stackLang
   prog's `Inst`/`If`/`ShMemOp` constructors
   (cakeml/compiler/encoders/asm/asmScript.sml):

     reg_imm = Reg reg | Imm ('a imm)          (imm = 'a word)   :74-76
     addr    = Addr reg ('a word)                                :121-123
     inst    = Skip | Const reg ('a word) | Arith ('a arith)
             | Mem memop reg ('a addr) | FP fp                  :130-136

   HOL indexes these by the word dimension `'a`; at the numeral type `64`
   the payloads are `64 word`, the faithful Lean counterparts being the
   width-indexed `HolRegImm`/`HolAddr`/`HolInst` in
   Flapjack/Compiler/Encoders/Asm.lean.  The rows below pin the constructor
   names, the `reg = num` fields, and the `64 word` payloads (bead
   flapjack-pxn.18.5.15.3.11.1).

   Provenance: generated from the Flapjack checkout with the
   coordinator-approved read-only prebuilt CakeML/HOL object directory as
   oracle input, without editing that checkout.  `asmTheory` is prebuilt in
   flapjack2/3/4/6, so the oracle checkout is flapjack2:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=asm_inst_fragment_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede. *)

val _ = print_eval "ar_reg"
  ``(case (asm$Reg 3 : 64 asm$reg_imm) of asm$Reg r => r | asm$Imm w => w2n w) : num``;
val _ = print_eval "ar_imm"
  ``(case (asm$Imm (5w : 64 word) : 64 asm$reg_imm) of asm$Reg r => r | asm$Imm w => w2n w) : num``;
val _ = print_eval "aa_base"
  ``(case (asm$Addr 3 (5w : 64 word) : 64 asm$addr) of asm$Addr r w => r) : num``;
val _ = print_eval "aa_off"
  ``(case (asm$Addr 3 (5w : 64 word) : 64 asm$addr) of asm$Addr r w => w2n w) : num``;
val _ = print_eval "ai_skip"
  ``(case (asm$Skip : 64 asm$inst) of asm$Skip => 1 | _ => 0) : num``;
val _ = print_eval "ai_const_reg"
  ``(case (asm$Const 2 (7w : 64 word) : 64 asm$inst) of asm$Const r w => r | _ => 0) : num``;
val _ = print_eval "ai_const_val"
  ``(case (asm$Const 2 (7w : 64 word) : 64 asm$inst) of asm$Const r w => w2n w | _ => 0) : num``;
val _ = print_eval "ai_mem_reg"
  ``(case (asm$Mem asm$Load 2 (asm$Addr 3 (5w : 64 word)) : 64 asm$inst)
      of asm$Mem m r a => r | _ => 0) : num``;
val _ = print_eval "ai_mem_base"
  ``(case (asm$Mem asm$Load 2 (asm$Addr 3 (5w : 64 word)) : 64 asm$inst)
      of asm$Mem m r a => (case a of asm$Addr b w => b) | _ => 0) : num``;

(* Monomorphic asm enums and the full `asm` datatype (bead .10.1). *)
val _ = print_eval "ab_add"
  ``(case (asm$Add : asm$binop) of asm$Add => 1 | asm$Sub => 2 | asm$And => 3 | asm$Or => 4 | asm$Xor => 5) : num``;
val _ = print_eval "ac_notTest"
  ``(case (asm$NotTest : asm$cmp) of
        asm$Equal => 0 | asm$Lower => 1 | asm$Less => 2 | asm$Test => 3
      | asm$NotEqual => 4 | asm$NotLower => 5 | asm$NotLess => 6 | asm$NotTest => 7) : num``;
val _ = print_eval "am_store32"
  ``(case (asm$Store32 : asm$memop) of
        asm$Load => 0 | asm$Load8 => 1 | asm$Load16 => 2 | asm$Load32 => 3
      | asm$Store => 4 | asm$Store8 => 5 | asm$Store16 => 6 | asm$Store32 => 7) : num``;
val _ = print_eval "aa_div_arity"
  ``(case (asm$Div 1 2 3 : 64 asm$arith) of asm$Div a b c => a + b + c | _ => 0) : num``;
val _ = print_eval "aa_longDiv_arity"
  ``(case (asm$LongDiv 1 2 3 4 5 : 64 asm$arith) of asm$LongDiv a b c d e => a+b+c+d+e | _ => 0) : num``;
val _ = print_eval "af_fpMovToReg"
  ``(case (asm$FPMovToReg 1 2 3 : asm$fp) of asm$FPMovToReg a b c => a + b + c | _ => 0) : num``;
val _ = print_eval "af_fpFromInt"
  ``(case (asm$FPFromInt 4 5 : asm$fp) of asm$FPFromInt a b => a + b | _ => 0) : num``;
val _ = print_eval "as_jump"
  ``(case (asm$Jump (9w : 64 word) : 64 asm$asm) of asm$Jump w => w2n w | _ => 0) : num``;
val _ = print_eval "as_jumpCmp"
  ``(case (asm$JumpCmp asm$Equal 1 (asm$Reg 2) (3w : 64 word) : 64 asm$asm)
      of asm$JumpCmp c r ri w => r | _ => 0) : num``;
val _ = print_eval "as_jumpReg"
  ``(case (asm$JumpReg 7 : 64 asm$asm) of asm$JumpReg r => r | _ => 0) : num``;
val _ = print_eval "as_loc"
  ``(case (asm$Loc 6 (8w : 64 word) : 64 asm$asm) of asm$Loc r w => r + w2n w | _ => 0) : num``;
