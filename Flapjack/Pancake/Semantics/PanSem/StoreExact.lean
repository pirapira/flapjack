import Flapjack.Pancake.Semantics.PanSem.AssignPrimitiveExact
import Flapjack.Pancake.Semantics.PanSem.MemLoadHOL
import Flapjack.Pancake.Semantics.PanSemStateEval

/-! # Exact panSem `Store`/`Store32`/`StoreByte` clause steps

HOL `panSem$evaluate` (`cakeml/pancake/semantics/panSemScript.sml`):

* `Store_` (`:583-589`): `case (eval s dst, eval s src) of
  (SOME (ValWord addr), SOME value) =>
  case mem_stores addr (flatten value) s.memaddrs s.memory of
  SOME m => (NONE, s with memory := m) | NONE => (SOME Error,s) | _ => (SOME Error,s)`.
* `Store32` (`:590-596`): both operands must be `ValWord`; writes `w2w w` with
  `mem_store_32 s.memory s.memaddrs s.be (w2w adr) (w2w w)`.
* `StoreByte` (`:597-603`): both operands must be `ValWord`; writes `w2w w` with
  `mem_store_byte s.memory s.memaddrs s.be (w2w adr) (w2w w)`.

These steps reuse the tagged exact `flattenHOL` (`flatten_def`), `panMemStoresHOL`
(`mem_stores_def`), `panMemStore32HOL` (`mem_store_32_def`) and
`panMemStoreByteHOL` (`mem_store_byte_def`).  They are deliberately **untagged**:
they are callback-parameterised clause infrastructure, not a statement-exact
`evaluate_def` port.  The direct original-HOL rows live in
`scripts/hol-probes/pan_sem_e2e_probe.out` (`store_clause_hit`,
`store_clause_out_of_domain`, `store32_clause_hit`, `storebyte_clause_hit`). -/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ExpHOL)

/-- Exact HOL `Store` clause step over the exact `PanSemStateExact` carrier. -/
def storeStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (destination source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state destination with
  | some (.val (.word address)) =>
      match evalExpression state source with
      | some value =>
          match panMemStoresHOL address (flattenHOL value) state.memaddrs state.memory with
          | some memory => (none, { state with memory := memory })
          | none => (some .error, state)
      | none => (some .error, state)
  | _ => (some .error, state)

/-- Exact HOL `Store32` clause step over the exact `PanSemStateExact` carrier. -/
def store32StepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state address with
  | some (.val (.word addr)) =>
      match evalExpression state value with
      | some (.val (.word word)) =>
          match panMemStore32HOL state.memory state.memaddrs state.be addr
              (BitVec.ofNat 32 word.toNat) with
          | some memory => (none, { state with memory := memory })
          | none => (some .error, state)
      | _ => (some .error, state)
  | _ => (some .error, state)

/-- Exact HOL `StoreByte` clause step over the exact `PanSemStateExact` carrier. -/
def storeByteStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state address with
  | some (.val (.word addr)) =>
      match evalExpression state value with
      | some (.val (.word word)) =>
          match panMemStoreByteHOL state.memory state.memaddrs state.be addr
              (UInt8.ofNat word.toNat) with
          | some memory => (none, { state with memory := memory })
          | none => (some .error, state)
      | _ => (some .error, state)
  | _ => (some .error, state)

end Flapjack
