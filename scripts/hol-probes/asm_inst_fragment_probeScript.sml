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
