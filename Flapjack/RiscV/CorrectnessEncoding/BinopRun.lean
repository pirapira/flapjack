import Flapjack.RiscV.CorrectnessEncoding.Length
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.Compiler.Encoders.AsmSem.Step
import Flapjack.RiscV.L3.Defs.Run

/-! Literal source and native register Binop compositions used to assemble the
full original encoder case at riscv_targetProofScript.sml:550-559. These local
compositions have no separately named HOL originals and remain untagged.
Every operator, both source operand constructors, all intrinsic native registers,
and the entire state are retained. No target execution premise is supplied. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.RiscV.Target
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Source post-state of the complete Binop constructor, derived solely from
original asm_step. Reads use the initial state, including destination aliases.
Untagged specialization of asm/inst/arith_upd and emitted-byte length. -/
theorem binop_source_post (op : HolBinop) (rd rs : Nat) (right : HolRegImm 64)
    (s1 s2 : AsmState 64)
    (h : asmStep riscvConfig s1 (.inst (.arith (.binop op rd rs right))) s2) :
    s2 = updPc (s1.pc + 4)
      (binopUpd rd op (readReg rs s1) (regImm right s1) s1) := by
  have step := h.2.2.2.2.1
  cases right <;> cases op <;>
    simpa [asmUpd, instUpd, arithUpd, riscvConfig, riscvEnc_length_eq,
      riscvAst, List.length_cons, List.length_nil] using step.symm

/-- Original five binary word operations, shared only by the local composition
below. No independent HOL declaration is claimed for this helper. -/
def binopValue (op : HolBinop) (left right : BitVec 64) : BitVec 64 :=
  match op with
  | .add => left + right
  | .sub => left - right
  | .and => left &&& right
  | .or => left ||| right
  | .xor => left ^^^ right

/-- Full native register Run equation for every original Binop operator. GPR
reads and write'GPR retain original zero-register and alias behavior; no input
bound, validity or successful execution hypothesis is needed. Untagged local
composition of original riscv_bop_r, Run and five dfn clauses. -/
theorem binop_register_run (op : HolBinop) (rd rs1 rs2 : BitVec 5)
    (ms : riscv_state) :
    Run (.ArithR (riscvBopR op (rd, rs1, rs2))) ms =
      «write'GPR» (binopValue op (GPR rs1 ms) (GPR rs2 ms), rd) ms := by
  cases op <;> rfl

end Flapjack.RiscV.TargetProof
