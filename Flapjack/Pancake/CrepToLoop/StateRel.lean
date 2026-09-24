import Flapjack.HolRef
import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.LoopStateResult

/-!
State relation of the Crepe-to-Loop lowering, ported from
`cakeml/pancake/proofs/crep_to_loopProofScript.sml` (the proof counterpart of
`crep_to_loopScript.sml`).  It relates the whole 11-field `crepSem$state`
(Lean `CrepHolState`) to the `loopSem$state` (Lean `LoopMachineState`).

Only the fields the relation constrains are compared; HOL's `memaddrs`/
`sh_memaddrs` are `set`s, rendered here as Boolean-valued membership maps
(`α → Bool`), matching the `mdomain`/`shMdomain` fields of `LoopMachineState`.
-/

namespace Flapjack

/-- Exact port of HOL `state_rel_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:28-36`):
    `state_rel s t` holds when the source and target states agree on the
    memory/stack domains, clock, endianness, FFI state, and base/top addresses.
    The remaining `CrepHolState` fields (`locals`, `globals`, `code`, `memory`)
    are related separately by `locals_rel`/`code_rel`/`mem_rel`/`globals_rel`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "state_rel_def"]
def crepToLoopStateRel {α σ : Type} (s : CrepHolState α σ)
    (t : LoopMachineState α σ) : Prop :=
  s.memaddrs = t.mdomain ∧
    s.shMemaddrs = t.shMdomain ∧
    s.clock = t.clock ∧
    s.bigEndian = t.be ∧
    s.ffi = t.ffi ∧
    s.baseAddress = t.baseAddr ∧
    s.topAddress = t.topAddr

/-- Exact port of HOL `state_rel_intro`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:163-174`): the relation
    unfolds to the same seven-field conjunction. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "state_rel_intro"]
theorem crepToLoopStateRel_intro {α σ : Type} (s : CrepHolState α σ)
    (t : LoopMachineState α σ) :
    crepToLoopStateRel s t ↔
      s.memaddrs = t.mdomain ∧
        s.shMemaddrs = t.shMdomain ∧
        s.clock = t.clock ∧
        s.bigEndian = t.be ∧
        s.ffi = t.ffi ∧
        s.baseAddress = t.baseAddr ∧
        s.topAddress = t.topAddr :=
  Iff.rfl

end Flapjack
