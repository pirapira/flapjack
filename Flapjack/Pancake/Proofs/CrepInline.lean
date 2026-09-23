import Flapjack.HolRef
import Flapjack.PanToCrepMaxList
import Flapjack.Pancake.Semantics.CrepSem

/-! Exact theorem counterpart for CakeML's `crep_inlineProofScript.sml`.

    The declarations here are stated over Lean's `(List.range n).map f`, the
    image of HOL's `GENLIST f n`, and over `Nat`, matching the source's
    `:num` variables. Each carries the HOL declaration name and argument
    order verbatim. -/

namespace Flapjack

/-- CakeML's `genlist_less_than` (`crep_inlineProofScript.sml:629`): every value
    in `GENLIST (λx. a + SUC x) n` is strictly above `a`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_less_than"]
theorem genlist_less_than (n a v : Nat) :
    v ∈ (List.range n).map (fun x => a + (x + 1)) → a < v := by
  intro hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_range] at hi
  omega

/-- CakeML's `genlist_not_in` (`crep_inlineProofScript.sml:636`): values at or
    below `a` do not occur in `GENLIST (λx. a + SUC x) n`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_not_in"]
theorem genlist_not_in (n a v : Nat) (h : v ≤ a) :
    v ∉ (List.range n).map (fun x => a + (x + 1)) := by
  intro hmem
  have := genlist_less_than n a v hmem
  omega

/-- CakeML's `genlist_all_distinct` (`crep_inlineProofScript.sml:643`):
    `GENLIST (λx. a + SUC x) n` has no duplicates. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "genlist_all_distinct"]
theorem genlist_all_distinct (n a : Nat) :
    ((List.range n).map (fun x => a + (x + 1))).Nodup :=
  List.Pairwise.map (fun x => a + (x + 1))
    (fun _left _right hne heq =>
      hne (Nat.add_right_cancel (Nat.add_left_cancel heq)))
    List.nodup_range

/-- CakeML's `MORE_THEN_NOT_MAX_LIST` (`crep_inlineProofScript.sml:1562`): a
    value strictly above `MAX_LIST l` does not occur in `l`.  Lean's `maxList`
    is the faithful port of HOL's `rich_list$MAX_LIST`
    (`Flapjack/PanToCrepMaxList.lean`), so this is the same fact as HOL's
    `MAX_LIST_NOT_MEM`, stated here under the `crep_inline` declaration name. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "MORE_THEN_NOT_MAX_LIST"]
theorem moreThenNotMaxList (l : List Nat) (x : Nat) (h : maxList l < x) :
    x ∉ l :=
  maxList_not_mem x l (by omega)

/-- CakeML's `max_list_genlist_add_suc_val`
    (`crep_inlineProofScript.sml:2579`): the maximum of
    `GENLIST (λx. SUC x + k) n` is `n + k` for `n ≠ 0`.  `(List.range n).map f`
    is Lean's image of HOL's `GENLIST f n`, and `maxList` is the faithful
    `rich_list$MAX_LIST` port (`Flapjack/PanToCrepMaxList.lean`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "max_list_genlist_add_suc_val"]
theorem max_list_genlist_add_suc_val (k : Nat) :
    ∀ n, n ≠ 0 →
      maxList ((List.range n).map (fun x => (x + 1) + k)) = n + k :=
  maxList_genlist_add_suc_val k

/-! ## State and locals relations of `inline_prog_correct` -/

/-- CakeML's `state_rel` (`crep_inlineProofScript.sml:12`): two Crep states agree
    on globals, code, memory, both address domains, clock, endianness, FFI
    state, and base/top addresses.  `CrepHolState` is the exact 11-field
    encoding of `crepSem$state`, so this is a field-by-field port; like HOL it
    leaves `locals` to `locals_rel`/`locals_strong_rel`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "state_rel_def"]
def crepInlineStateRel (s t : CrepHolState α σ) : Prop :=
  s.globals = t.globals ∧
  s.code = t.code ∧
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.shMemaddrs = t.shMemaddrs ∧
  s.clock = t.clock ∧
  s.bigEndian = t.bigEndian ∧
  s.ffi = t.ffi ∧
  s.baseAddress = t.baseAddress ∧
  s.topAddress = t.topAddress

/-- Finite-map `SUBMAP` for Lean's extensional lookup-function representation:
    every binding of `s` is also a binding of `t` with the same value.  HOL's
    `SUBMAP` holds when `FLOOKUP s` and `FLOOKUP t` agree on `FDOM s`, which is
    exactly this statement.  Untagged infrastructure: HOL's `SUBMAP` is a
    finite-map operation, not a declaration of `crep_inlineProofScript.sml`. -/
def crepHolSubmap (s t : Nat → Option β) : Prop :=
  ∀ n v, s n = some v → t n = some v

/-- CakeML's `locals_rel` (`crep_inlineProofScript.sml:26`):
    `s.locals SUBMAP t.locals`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_rel_def"]
def crepInlineLocalsRel (s t : CrepHolState α σ) : Prop :=
  crepHolSubmap s.locals t.locals

/-- CakeML's `locals_strong_rel` (`crep_inlineProofScript.sml:31`):
    `s.locals = t.locals`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_strong_rel_def"]
def crepInlineLocalsStrongRel (s t : CrepHolState α σ) : Prop :=
  s.locals = t.locals

/-- CakeML's `locals_rel_dec_clock` (`crep_inlineProofScript.sml:167`): both
    relations are preserved by `dec_clock`, since only `clock` changes. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "locals_rel_dec_clock"]
theorem crepInlineLocalsRel_decClock (s t : CrepHolState α σ)
    (hlocals : crepInlineLocalsRel s t) (hstate : crepInlineStateRel s t) :
    crepInlineLocalsRel (decCrepHolClock s) (decCrepHolClock t) ∧
    crepInlineStateRel (decCrepHolClock s) (decCrepHolClock t) := by
  obtain ⟨hg, hc, hm, hma, hsm, hcl, hbe, hf, hba, hta⟩ := hstate
  refine ⟨?_, ?_⟩
  · simpa only [crepInlineLocalsRel, decCrepHolClock] using hlocals
  · simp only [crepInlineStateRel, decCrepHolClock]
    exact ⟨hg, hc, hm, hma, hsm, by rw [hcl], hbe, hf, hba, hta⟩

end Flapjack
