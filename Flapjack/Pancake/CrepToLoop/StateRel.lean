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
(`BitVec width → Bool`), matching the `mdomain`/`shMdomain` fields of
`LoopMachineState`.

Every tagged declaration is width-specialized to `BitVec width`: HOL
`crepSem$state`/`loopSem$state` are word-length indexed (`'a word` fields), so
a generic-`α` carrier is not an exact counterpart.
-/

namespace Flapjack

/-- Exact port of HOL `state_rel_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:28-36`):
    `state_rel s t` holds when the source and target states agree on the
    memory/stack domains, clock, endianness, FFI state, and base/top addresses.
    The remaining `CrepHolState` fields (`locals`, `globals`, `code`, `memory`)
    are related separately by `locals_rel`/`code_rel`/`mem_rel`/`globals_rel`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "state_rel_def"]
def crepToLoopStateRel {width : Nat} {σ : Type} (s : CrepHolState (BitVec width) σ)
    (t : LoopMachineState (BitVec width) σ) : Prop :=
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
theorem crepToLoopStateRel_intro {width : Nat} {σ : Type} (s : CrepHolState (BitVec width) σ)
    (t : LoopMachineState (BitVec width) σ) :
    crepToLoopStateRel s t ↔
      s.memaddrs = t.mdomain ∧
        s.shMemaddrs = t.shMdomain ∧
        s.clock = t.clock ∧
        s.bigEndian = t.be ∧
        s.ffi = t.ffi ∧
        s.baseAddress = t.baseAddr ∧
        s.topAddress = t.topAddr :=
  Iff.rfl

/-- Exact port of HOL `wlab_wloc_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:45-47`):
    `wlab_wloc (panSem$Word w) = wordLang$Word w`. `PanWordLab` and `LoopValue`
    both have a single `word` constructor for word payloads, so the map is the
    identity on the word. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "wlab_wloc_def"]
def wlabWloc {width : Nat} : PanWordLab (BitVec width) → LoopValue (BitVec width)
  | .word value => .word value

/-- Exact port of HOL `globals_rel_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:54-58`): every source
    global lookup is matched by the target's `wlab_wloc` image.  HOL's
    `FLOOKUP` on `5 word |-> 'a word_loc` is the target field application;
    the source `globals` is the same `BitVec 5`-indexed option finite map. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "globals_rel_def"]
def crepToLoopGlobalsRel {width : Nat}
    (sglobals : BitVec 5 → Option (PanWordLab (BitVec width)))
    (tglobals : BitVec 5 → Option (LoopValue (BitVec width))) : Prop :=
  ∀ address value, sglobals address = some value → tglobals address = some (wlabWloc value)

/-- Exact port of HOL `globals_rel_intro`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:203-209`), which is an
    implication: assuming the relation, unpack the universally quantified
    lookup agreement. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "globals_rel_intro"]
theorem crepToLoopGlobalsRel_intro {width : Nat}
    (sglobals : BitVec 5 → Option (PanWordLab (BitVec width)))
    (tglobals : BitVec 5 → Option (LoopValue (BitVec width)))
    (h : crepToLoopGlobalsRel sglobals tglobals) :
    ∀ address value, sglobals address = some value → tglobals address = some (wlabWloc value) :=
  fun address value hv => h address value hv

/-- Untagged iff form of `crepToLoopGlobalsRel`, kept for rewriting/rewriting
    the relation to its unfolded implication. -/
theorem crepToLoopGlobalsRel_iff {width : Nat}
    (sglobals : BitVec 5 → Option (PanWordLab (BitVec width)))
    (tglobals : BitVec 5 → Option (LoopValue (BitVec width))) :
    crepToLoopGlobalsRel sglobals tglobals ↔
      ∀ address value, sglobals address = some value → tglobals address = some (wlabWloc value) :=
  Iff.rfl

/-- Exact port of HOL `state_rel_clock_add_zero`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:219-223`): a state
    relation is preserved when the target clock is advanced by zero. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "state_rel_clock_add_zero"]
theorem crepToLoopStateRel_clock_add_zero {width : Nat} {σ : Type}
    (s : CrepHolState (BitVec width) σ)
    (t : LoopMachineState (BitVec width) σ) (h : crepToLoopStateRel s t) :
    ∃ ck, crepToLoopStateRel s { t with clock := ck + t.clock } :=
  ⟨0, by
    rw [crepToLoopStateRel] at h ⊢
    simpa using h⟩

end Flapjack
