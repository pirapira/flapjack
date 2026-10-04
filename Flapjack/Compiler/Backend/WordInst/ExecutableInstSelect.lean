import Flapjack.Compiler.Backend.WordInst.ExecutablePullExp

/-! Flapjack execution infrastructure for the complete native instruction
selector. This keeps every original selector clause, using the unconditionally
checked executable pullExp. Original tagged definitions remain unchanged.
The agreement is within Lean; original HOL probes are independent regressions,
not cross-language equivalence proofs. -/

namespace Flapjack.Compiler.Backend.WordInst
open Flapjack Flapjack.Compiler.Encoders.Asm ExecutablePullExp

/-- Executable full selector, with the original offsets, source traversal,
Call continuations and handlers. No success or well-formedness premise is used.
Untagged implementation infrastructure, related to the source port below. -/
def instSelectExecutable {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp : Nat) : WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width)
  | .assign v exp => instSelectExp c v temp (flattenExp (pullExpExecutable exp))
  | .set store exp =>
      let prog := instSelectExp c temp temp (flattenExp (pullExpExecutable exp))
      .seq prog (.set store (.var temp))
  | .store exp var =>
      let exp := flattenExp (pullExpExecutable exp)
      match exp with
      | .op .add [exp', .const w] =>
          if addrOffsetOk c w then
            let prog := instSelectExp c temp temp exp'
            .seq prog (.inst (.mem .store var (.addr temp w)))
          else
            let prog := instSelectExp c temp temp exp
            .seq prog (.inst (.mem .store var (.addr temp 0)))
      | _ =>
          let prog := instSelectExp c temp temp exp
          .seq prog (.inst (.mem .store var (.addr temp 0)))
  | .seq p1 p2 => .seq (instSelectExecutable c temp p1) (instSelectExecutable c temp p2)
  | .mustTerminate p1 => .mustTerminate (instSelectExecutable c temp p1)
  | .shareInst op v exp =>
      let exp := flattenExp (pullExpExecutable exp)
      match exp with
      | .op .add [exp', .const w] =>
          if ((op = .load ∨ op = .store) ∧ addrOffsetOk c w) ∨
              ((op = .load32 ∨ op = .store32) ∧ addrOffsetOk c w) ∨
              ((op = .load16 ∨ op = .store16) ∧ hwOffsetOk c w) ∨
              ((op = .load8 ∨ op = .store8) ∧ byteOffsetOk c w) then
            let prog := instSelectExp c temp temp exp'
            .seq prog (.shareInst op v (.op .add [.var temp, .const w]))
          else
            let prog := instSelectExp c temp temp exp
            .seq prog (.shareInst op v (.var temp))
      | _ =>
          let prog := instSelectExp c temp temp exp
          .seq prog (.shareInst op v (.var temp))
  | .ite cmp r1 ri c1 c2 => .ite cmp r1 ri (instSelectExecutable c temp c1) (instSelectExecutable c temp c2)
  | .call ret dest args handler =>
      let retsel :=
        match ret with
        | none => none
        | some (n, names, retHandler, l1, l2) => some (n, names, instSelectExecutable c temp retHandler, l1, l2)
      let handlersel :=
        match handler with
        | none => none
        | some (n, h, l1, l2) => some (n, instSelectExecutable c temp h, l1, l2)
      .call retsel dest args handlersel
  | .loop names body exitNames => .loop names (instSelectExecutable c temp body) exitNames
  | prog => prog

/-- Full unconditional agreement with the native source selector, for every
positive width, asm configuration, temporary register and native program.
This is Flapjack computation infrastructure, with no separate HOL original. -/
theorem instSelectExecutable_eq {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (temp : Nat) (program : WordLangProgHOL (BitVec width)) :
    instSelectExecutable c temp program = instSelect c temp program := by
  refine (measure (sizeOf : WordLangProgHOL (BitVec width) → Nat)).wf.induction
    (C := fun p => instSelectExecutable c temp p = instSelect c temp p) program ?_
  intro p ih
  cases p
  all_goals try simp only [instSelectExecutable, instSelect, pullExpExecutable_eq]
  all_goals try rfl
  case mustTerminate body =>
    rw [ih body (by change sizeOf body < sizeOf (WordLangProgHOL.mustTerminate body); simp_wf)]
  case seq first second =>
    rw [ih first (by change sizeOf first < sizeOf (WordLangProgHOL.seq first second); simp_wf; omega),
      ih second (by change sizeOf second < sizeOf (WordLangProgHOL.seq first second); simp_wf; omega)]
  case ite op r ri yes no =>
    rw [ih yes (by change sizeOf yes < sizeOf (WordLangProgHOL.ite op r ri yes no); simp_wf; omega),
      ih no (by change sizeOf no < sizeOf (WordLangProgHOL.ite op r ri yes no); simp_wf; omega)]
  case loop names body exits =>
    rw [ih body (by change sizeOf body < sizeOf (WordLangProgHOL.loop names body exits); simp_wf; omega)]
  case call ret dest args handler =>
    rcases ret with _ | ⟨n, names, retProg, l1, l2⟩ <;>
      rcases handler with _ | ⟨hn, handlerProg, h1, h2⟩ <;>
      simp only [instSelectExecutable, instSelect]
    all_goals first
      | rfl
      | (congr 6 <;> apply ih <;> change sizeOf _ < sizeOf _ <;> simp_wf <;> omega)

end Flapjack.Compiler.Backend.WordInst
