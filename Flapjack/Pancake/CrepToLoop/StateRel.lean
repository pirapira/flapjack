import Flapjack.HolRef
import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.ByteAlignBridge
import Flapjack.LoopStateResult
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Misc.Sptree

/-!
State relation analogue for the Crepe-to-Loop lowering, based on
`cakeml/pancake/proofs/crep_to_loopProofScript.sml` (the proof counterpart of
`crep_to_loopScript.sml`). The production-state relation below is not an exact
HOL `state_rel` port: `CrepHolState` and `LoopMachineState` have String-backed
code names, and the latter uses list/option fields where HOL uses finite maps
and total functions. Standalone memory/global relations over exact field
carriers remain tagged where appropriate.

Only the fields the relation constrains are compared; HOL's `memaddrs`/
`sh_memaddrs` are `set`s, rendered here as Boolean-valued membership maps
(`BitVec width → Bool`), matching the `mdomain`/`shMdomain` fields of
`LoopMachineState`.

Tagged declarations that compare word-typed fields directly are width-specialized
to `BitVec width`, because HOL `crepSem$state`/`loopSem$state` are word-length
indexed (`'a word` fields) and a generic-`α` carrier would not be an exact
counterpart; those declarations carry `[NeZero width]`, because HOL word types
have positive `dimindex` while `BitVec 0` is inhabited and has no HOL
counterpart.  The relations over pure `num`/`num` finite maps (`distinct_funcs`,
`distinct_vars`, `ctxt_max`) are polymorphic exactly as the un-annotated HOL
`Definition`s infer them (key, and value where no arithmetic constrains it).
-/

namespace Flapjack

/-! The Cake theorem `mem_lookup_fromalist_some` is stated in this proof
counterpart, while the generic `sptFromAList` rendering stays with the Spt
carrier in `Flapjack.Misc.Sptree`. The helpers below are local proof support
for this theorem. -/

/-- Same-key lookup after insertion, proved by strong induction on the HOL
binary-tree key recursion. -/
private theorem sptLookup_sptInsert_same {α : Type} :
    ∀ (key : Nat) (value : α) (tree : Spt α),
      sptLookup key (sptInsert key value tree) = some value := by
  intro key
  induction key using Nat.strongRecOn with
  | ind key ih =>
      intro value tree
      by_cases hzero : key = 0
      · subst key
        exact sptLookup_sptInsert_zero value tree
      · have hpositive : 0 < key := Nat.pos_of_ne_zero hzero
        have hdecrease : (key - 1) / 2 < key := by
          have hdiv : (key - 1) / 2 ≤ key - 1 := Nat.div_le_self _ _
          have hlt : key - 1 < key := Nat.sub_lt hpositive (by decide)
          omega
        by_cases heven : key % 2 = 0
        · cases tree with
          | ln =>
              conv => lhs; rw [sptInsert.eq_1, if_neg hzero, if_pos heven]
              conv => lhs; rw [sptLookup.eq_3, if_neg hzero, if_pos heven]
              exact ih ((key - 1) / 2) hdecrease value .ln
          | ls existing =>
              conv => lhs; rw [sptInsert.eq_2, if_neg hzero, if_pos heven]
              conv => lhs; rw [sptLookup.eq_4, if_neg hzero, if_pos heven]
              exact ih ((key - 1) / 2) hdecrease value .ln
          | bn left right =>
              conv => lhs; rw [sptInsert.eq_3, if_neg hzero, if_pos heven]
              conv => lhs; rw [sptLookup.eq_3, if_neg hzero, if_pos heven]
              exact ih ((key - 1) / 2) hdecrease value left
          | bs left existing right =>
              conv => lhs; rw [sptInsert.eq_4, if_neg hzero, if_pos heven]
              conv => lhs; rw [sptLookup.eq_4, if_neg hzero, if_pos heven]
              exact ih ((key - 1) / 2) hdecrease value left
        · cases tree with
          | ln =>
              conv => lhs; rw [sptInsert.eq_1, if_neg hzero, if_neg heven]
              conv => lhs; rw [sptLookup.eq_3, if_neg hzero, if_neg heven]
              exact ih ((key - 1) / 2) hdecrease value .ln
          | ls existing =>
              conv => lhs; rw [sptInsert.eq_2, if_neg hzero, if_neg heven]
              conv => lhs; rw [sptLookup.eq_4, if_neg hzero, if_neg heven]
              exact ih ((key - 1) / 2) hdecrease value .ln
          | bn left right =>
              conv => lhs; rw [sptInsert.eq_3, if_neg hzero, if_neg heven]
              conv => lhs; rw [sptLookup.eq_3, if_neg hzero, if_neg heven]
              exact ih ((key - 1) / 2) hdecrease value right
          | bs left existing right =>
              conv => lhs; rw [sptInsert.eq_4, if_neg hzero, if_neg heven]
              conv => lhs; rw [sptLookup.eq_4, if_neg hzero, if_neg heven]
              exact ih ((key - 1) / 2) hdecrease value right

private theorem sptFromAList_mem_insert {α : Type}
    {entries : List (Nat × α)} {key : Nat} {value : α}
    (hnodup : (entries.map Prod.fst).Nodup)
    (hmem : (key, value) ∈ entries) :
    ∃ tree, sptFromAList entries = sptInsert key value tree := by
  induction entries with
  | nil => simp at hmem
  | cons entry entries ih =>
      obtain ⟨headKey, headValue⟩ := entry
      rcases List.nodup_cons.mp hnodup with ⟨hheadNot, htailNodup⟩
      rcases List.mem_cons.mp hmem with hhead | htail
      · have hpair : headKey = key ∧ headValue = value := by
          simpa using hhead.symm
        rcases hpair with ⟨hkey, hvalue⟩
        subst key
        subst value
        exact ⟨sptFromAList entries, rfl⟩
      · have hkeyMem : key ∈ entries.map Prod.fst := by
          simp only [List.mem_map]
          exact ⟨(key, value), htail, rfl⟩
        have hheadNe : headKey ≠ key := by
          intro heq
          subst headKey
          exact hheadNot hkeyMem
        obtain ⟨tree, htree⟩ := ih htailNodup htail
        refine ⟨sptInsert headKey headValue tree, ?_⟩
        change sptInsert headKey headValue (sptFromAList entries) =
          sptInsert key value (sptInsert headKey headValue tree)
        rw [htree]
        exact sptInsert_swap headKey key headValue value tree hheadNe

/-- Exact port of CakeML `mem_lookup_fromalist_some`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3813`). For a distinct
    key list, every member association is returned by HOL `lookup` after
    `fromAList`. The premises and conclusion match the HOL theorem; the
    association-list recursion uses the exact Spt rendering imported from
    `Flapjack.Misc.Sptree`, with no list-lookup substitute. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "mem_lookup_fromalist_some"]
theorem memLookupFromAListSomeExact {α : Type}
    {entries : List (Nat × α)} {key : Nat} {value : α}
    (hnodup : (entries.map Prod.fst).Nodup)
    (hmem : (key, value) ∈ entries) :
    sptLookup key (sptFromAList entries) = some value := by
  obtain ⟨tree, htree⟩ := sptFromAList_mem_insert hnodup hmem
  rw [htree]
  exact sptLookup_sptInsert_same key value tree

/-- Flapjack analogue of HOL `state_rel_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:28-36`):
    `state_rel s t <=> s.memaddrs = t.mdomain /\ s.sh_memaddrs = t.sh_mdomain /\
    s.clock = t.clock /\ s.be = t.be /\ s.ffi = t.ffi /\ s.base_addr = t.base_addr /\
    s.top_addr = t.top_addr`.

    The relation's seven field equations match HOL clause-for-clause, but the tag
    stays **withdrawn** for a substantive carrier mismatch. HOL's operands are
    `('a,'ffi) crepSem$state` and `('a,'ffi) loopSem$state`, whose code maps are
    keyed by `mlstring` (`funname`), whose memory is a total
    `'a word -> 'a word_lab`/`word_loc` function, and whose fields are spelled
    `sh_memaddrs`/`be`/`base_addr`/`top_addr`. The Flapjack `CrepHolState` and
    `LoopMachineState` are production carriers: their code maps use
    `FunName = String` and their memory representations differ, so the
    quantified state types (not just the fields read) are mismatched.
    `names_as_string` cannot authorise a different state carrier (it covers only
    identifier-representing names), and no same-module `NameRanged` byte witness
    applies because the conclusion is a `Prop`, not a name.

    Direct HOL oracle: `scripts/hol-probes/crep_to_loop_state_rel_probe.out`
    rows `memaddrs_mdomain_mem`, `sh_memaddrs_sh_mdomain_mem`, `clock_eq`,
    `be_eq`, `base_eq`, `top_eq`, `clock_mismatch`. Faithful exact-carrier port
    is tracked by `flapjack-pxn.18.5.6.9.1`. -/
def crepToLoopStateRel {width : Nat} [NeZero width] {σ : Type} (s : CrepHolState (BitVec width) σ)
    (t : LoopMachineState (BitVec width) σ) : Prop :=
  s.memaddrs = t.mdomain ∧
    s.shMemaddrs = t.shMdomain ∧
    s.clock = t.clock ∧
    s.bigEndian = t.be ∧
    s.ffi = t.ffi ∧
    s.baseAddress = t.baseAddr ∧
    s.topAddress = t.topAddr

/-- Flapjack analogue of HOL `state_rel_intro`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:163-174`), the field
    expansion of `state_rel_def` (`s.memaddrs = t.mdomain /\
    s.sh_memaddrs = t.sh_mdomain /\ s.clock = t.clock /\ s.be = t.be /\
    s.ffi = t.ffi /\ s.base_addr = t.base_addr /\ s.top_addr = t.top_addr`).

    The seven equations match HOL clause-for-clause; like HOL (whose
    `state_rel_intro` is an `<=>`), the Flapjack version is stated as an `↔`.
    The tag
    stays **withdrawn** for the same substantive carrier mismatch as
    `crepToLoopStateRel`: HOL quantifies `mlstring`-keyed
    `crepSem$state`/`loopSem$state`, while Flapjack quantifies the production
    `CrepHolState`/`LoopMachineState` with `FunName = String` code maps and
    different memory representations. `names_as_string` cannot authorise a
    different state carrier, and no `NameRanged` byte witness applies because
    the conclusion is a `Prop`/iff, not a name. Direct HOL oracle:
    `scripts/hol-probes/crep_to_loop_state_rel_probe.out` rows
    `memaddrs_mdomain_mem`, `sh_memaddrs_sh_mdomain_mem`, `clock_eq`, `be_eq`,
    `base_eq`, `top_eq`, `clock_mismatch`. Faithful exact-carrier port is
    tracked by `flapjack-pxn.18.5.6.9.1`. -/
theorem crepToLoopStateRel_intro {width : Nat} [NeZero width] {σ : Type} (s : CrepHolState (BitVec width) σ)
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
def wlabWloc {width : Nat} [NeZero width] : PanWordLab (BitVec width) → LoopValue (BitVec width)
  | .word value => .word value

/-- Exact port of HOL `globals_rel_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:54-58`): every source
    global lookup is matched by the target's `wlab_wloc` image.  HOL's
    `FLOOKUP` on `5 word |-> 'a word_loc` is the target field application;
    the source `globals` is the same `BitVec 5`-indexed option finite map. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "globals_rel_def"]
def crepToLoopGlobalsRel {width : Nat} [NeZero width]
    (sglobals : BitVec 5 → Option (PanWordLab (BitVec width)))
    (tglobals : BitVec 5 → Option (LoopValue (BitVec width))) : Prop :=
  ∀ address value, sglobals address = some value → tglobals address = some (wlabWloc value)

/-- Exact port of HOL `globals_rel_intro`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:203-209`), which is an
    implication: assuming the relation, unpack the universally quantified
    lookup agreement. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "globals_rel_intro"]
theorem crepToLoopGlobalsRel_intro {width : Nat} [NeZero width]
    (sglobals : BitVec 5 → Option (PanWordLab (BitVec width)))
    (tglobals : BitVec 5 → Option (LoopValue (BitVec width)))
    (h : crepToLoopGlobalsRel sglobals tglobals) :
    ∀ address value, sglobals address = some value → tglobals address = some (wlabWloc value) :=
  fun address value hv => h address value hv

/-- Untagged iff form of `crepToLoopGlobalsRel`, kept for rewriting/rewriting
    the relation to its unfolded implication. -/
theorem crepToLoopGlobalsRel_iff {width : Nat} [NeZero width]
    (sglobals : BitVec 5 → Option (PanWordLab (BitVec width)))
    (tglobals : BitVec 5 → Option (LoopValue (BitVec width))) :
    crepToLoopGlobalsRel sglobals tglobals ↔
      ∀ address value, sglobals address = some value → tglobals address = some (wlabWloc value) :=
  Iff.rfl

/-- Flapjack analogue of HOL `state_rel_clock_add_zero`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:219-223`):
    `!s t. state_rel s t ==> ?ck. state_rel s (t with clock := ck + t.clock)`.

    The statement shape is identical (a single preservation implication whose
    witness is the fresh clock `ck`), but the tag stays **withdrawn** for a
    substantive carrier mismatch. HOL quantifies `('a,'ffi) crepSem$state` and
    `('a,'ffi) loopSem$state`, whose code maps are keyed by `mlstring`
    (`funname`) and whose memories are total functions/`mlstring`-keyed finite
    maps. The Flapjack declarations quantify the production `CrepHolState` and
    `LoopMachineState`, whose code maps use `FunName = String` and whose memory
    representation differs; those carriers appear in the quantified state types
    even though `state_rel` itself only reads seven fields, so per AGENTS.md the
    general parameterisation is a mismatch. `names_as_string` cannot authorise a
    different state carrier (only identifier-representing names), and no
    same-module `NameRanged` byte witness applies because the conclusion is a
    `Prop` (an existential over clocks), not a name.

    Direct HOL oracle: `scripts/hol-probes/crep_to_loop_state_rel_probe.out`
    rows `memaddrs_mdomain_mem`, `sh_memaddrs_sh_mdomain_mem`, `clock_eq`,
    `be_eq`, `base_eq`, `top_eq`, `clock_mismatch` pin the seven-field relation;
    the theorem is exercised by the kernel-checked example in
    `Flapjack/Test/CrepToLoopParity.lean` (`state_rel_clock_add_zero`,
    ~lines 363-368). Faithful exact-carrier port is tracked by
    `flapjack-pxn.18.5.6.9.1`. -/
theorem crepToLoopStateRel_clock_add_zero {width : Nat} [NeZero width] {σ : Type}
    (s : CrepHolState (BitVec width) σ)
    (t : LoopMachineState (BitVec width) σ) (h : crepToLoopStateRel s t) :
    ∃ ck, crepToLoopStateRel s { t with clock := ck + t.clock } :=
  ⟨0, by
    rw [crepToLoopStateRel] at h ⊢
    simpa using h⟩

/-- Exact port of HOL `mem_rel_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:49-52`):
    `mem_rel smem tmem dom <=> !ad. ad IN dom ==> wlab_wloc (smem ad) = tmem ad`.

    HOL's `loopSem$state.memory` is TOTAL (`'a word → 'a word_loc`) and the
    crep side is already total (`crepSem$state.memory : 'a word → 'a word_lab`),
    so the relation is stated over total memories. `LoopMachineState.memory` is
    Option-valued, so production instantiates the target memory through the
    total view `loopMemoryTotal default t` below; `mem_rel` only constrains
    addresses in `dom`, where the view agrees with the `some`-defined field.
    HOL's `ad IN dom` is the set-as-predicate rendering `dom ad = true`, matching
    the `mdomain`/`shMdomain` fields. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "mem_rel_def"]
def crepToLoopMemRel {width : Nat} [NeZero width]
    (smem : BitVec width → PanWordLab (BitVec width))
    (tmem : BitVec width → LoopValue (BitVec width))
    (dom : BitVec width → Bool) : Prop :=
  ∀ ad, dom ad = true → wlabWloc (smem ad) = tmem ad

/-- Exact port of HOL `mem_rel_intro`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:203-209`), which is an
    implication: assuming `mem_rel`, unpack the pointwise lookup equation. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "mem_rel_intro"]
theorem crepToLoopMemRel_intro {width : Nat} [NeZero width]
    (smem : BitVec width → PanWordLab (BitVec width))
    (tmem : BitVec width → LoopValue (BitVec width))
    (dom : BitVec width → Bool)
    (h : crepToLoopMemRel smem tmem dom) :
    ∀ ad, dom ad = true → wlabWloc (smem ad) = tmem ad :=
  fun ad hd => h ad hd

/-- Untagged iff form of `crepToLoopMemRel`, kept for rewriting. -/
theorem crepToLoopMemRel_iff {width : Nat} [NeZero width]
    (smem : BitVec width → PanWordLab (BitVec width))
    (tmem : BitVec width → LoopValue (BitVec width))
    (dom : BitVec width → Bool) :
    crepToLoopMemRel smem tmem dom ↔
      ∀ ad, dom ad = true → wlabWloc (smem ad) = tmem ad :=
  Iff.rfl

/-- Total view of the Option-valued `LoopMachineState.memory`, giving the total
    target memory that HOL's `loopSem$state.memory` has. Since `mem_rel` only
    constrains addresses in its `dom`, the `default` value at unset addresses is
    irrelevant. -/
def loopMemoryTotal {W F : Type} (default : LoopValue W)
    (t : LoopMachineState W F) : W → LoopValue W :=
  fun ad => (t.memory ad).getD default

/-- Kernel-checked total-view bridge: at a defined address the total view agrees
    with the Option-valued `LoopMachineState.memory` field. -/
theorem loopMemoryTotal_eq_some {W F : Type} (default : LoopValue W)
    (t : LoopMachineState W F) (ad : W) (v : LoopValue W)
    (h : t.memory ad = some v) : loopMemoryTotal default t ad = v := by
  simp [loopMemoryTotal, h]

/-- Exact port of HOL `crep_to_loop$distinct_funcs_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:60-65`): distinct
    function-map keys are separated by their target labels, so two entries with
    equal labels must share the key.  HOL's un-annotated `Definition` infers
    `fm : 'a |-> ('b # 'c)`, so the Lean port is polymorphic in the key and in
    both tuple components (exactly the inferred HOL polymorphism). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "distinct_funcs_def"]
def crepToLoopDistinctFuncs {κ α β : Type} (functions : FiniteMap κ (α × β)) : Prop :=
  ∀ (x y : κ) (n m : α) (rm rm' : β),
    FLOOKUP functions x = some (n, rm) →
    FLOOKUP functions y = some (m, rm') → n = m → x = y

/-- Untagged iff form of `crepToLoopDistinctFuncs`, kept for rewriting. -/
theorem crepToLoopDistinctFuncs_iff {κ α β : Type} (functions : FiniteMap κ (α × β)) :
    crepToLoopDistinctFuncs functions ↔
      ∀ (x y : κ) (n m : α) (rm rm' : β),
        FLOOKUP functions x = some (n, rm) →
        FLOOKUP functions y = some (m, rm') → n = m → x = y :=
  Iff.rfl

/-- Exact port of HOL `crep_to_loop$distinct_vars_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:95-99`): distinct
    variable-map keys are separated by their local slot, so two entries with
    equal slots must share the key.  HOL's un-annotated `Definition` infers
    `fm : 'a |-> 'b`, so the Lean port is polymorphic in the key and the value
    (exactly the inferred HOL polymorphism). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "distinct_vars_def"]
def crepToLoopDistinctVars {κ β : Type} (vars : FiniteMap κ β) : Prop :=
  ∀ (x y : κ) (n m : β),
    FLOOKUP vars x = some n → FLOOKUP vars y = some m → n = m → x = y

/-- Untagged iff form of `crepToLoopDistinctVars`, kept for rewriting. -/
theorem crepToLoopDistinctVars_iff {κ β : Type} (vars : FiniteMap κ β) :
    crepToLoopDistinctVars vars ↔
      ∀ (x y : κ) (n m : β),
        FLOOKUP vars x = some n → FLOOKUP vars y = some m → n = m → x = y :=
  Iff.rfl

/-- Exact port of HOL `crep_to_loop$ctxt_max_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:90-93`): every value
    stored in the map is bounded by `n`.  HOL's un-annotated `Definition` infers
    `fm : 'a |-> num` (`m <= n` constrains the values to `num`), so the Lean
    port is polymorphic in the key and fixed at `Nat` for the values. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ctxt_max_def"]
def crepToLoopCtxtMax {κ : Type} (n : Nat) (fm : FiniteMap κ Nat) : Prop :=
  ∀ (v : κ) (m : Nat), FLOOKUP fm v = some m → m ≤ n

/-- Untagged iff form of `crepToLoopCtxtMax`, kept for rewriting. -/
theorem crepToLoopCtxtMax_iff {κ : Type} (n : Nat) (fm : FiniteMap κ Nat) :
    crepToLoopCtxtMax n fm ↔ ∀ (v : κ) (m : Nat), FLOOKUP fm v = some m → m ≤ n :=
  Iff.rfl

/-! ## `locals_rel` (untagged production analogue)

HOL `locals_rel_def`
(`cakeml/pancake/proofs/crep_to_loopProofScript.sml:101-111`) is stated over

    locals_rel ctxt (l:sptree$num_set) (s_locals:num |-> 'a word_lab) t_locals <=>
      distinct_vars ctxt.vars /\\ ctxt_max ctxt.vmax ctxt.vars /\\
      domain l ⊆ domain t_locals /\\
      ∀vname v. FLOOKUP s_locals vname = SOME v =>
        ?n. FLOOKUP ctxt.vars vname = SOME n /\\ n ∈ domain l /\\
            lookup n t_locals = SOME (wlab_wloc v)

The Lean port below reproduces every side condition, but it is deliberately
**not** tagged, because three HOL carriers do not yet have exact Lean
counterparts:

* `ctxt.vars : num |-> num` (a finite map) versus the Lean
  `LoopContext.vars : NatInfoMap Nat = List (Nat × Nat)` (list-backed,
  first-match lookup) — so `distinct_vars ctxt.vars` / `ctxt_max ctxt.vmax
  ctxt.vars` / `FLOOKUP ctxt.vars vname` are rendered with `lookupNatInfo`;
* `l : sptree$num_set` (with `domain l` and `n ∈ domain l`) versus a Boolean
  membership function `live : Nat → Bool` (the same set-as-membership-map
  rendering used for `memaddrs`/`sh_memaddrs`);
* `t_locals : sptree$num_map` (with `lookup n t_locals`) versus the flat
  function `LoopMachineState.locals : Nat → Option (LoopValue W)`, so
  `domain l ⊆ domain t_locals` becomes `live n = true → (tLocals n).isSome`
  and `lookup n t_locals = SOME w` becomes `tLocals n = some w`.

The finite-map-shaped analogue `crepToLoopLocalsRelHOL` below uses
`CrepToLoopFiniteMapContext`; it still has the `funcs` key mismatch documented
below and is also untagged. This list-backed rendering remains for production
clients. -/

/-- Untagged faithful-shape rendering of HOL `crep_to_loop$locals_rel_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:101-111`); see the
    section note above for the three carrier gaps that withhold the HOL tag. -/
def crepToLoopLocalsRel {width : Nat} [NeZero width] {α : Type} (context : LoopContext α)
    (live : Nat → Bool)
    (sLocals : FiniteMap Nat (PanWordLab (BitVec width)))
    (tLocals : Nat → Option (LoopValue (BitVec width))) : Prop :=
  (∀ x y n m,
      lookupNatInfo x context.vars = some n →
      lookupNatInfo y context.vars = some m → n = m → x = y) ∧
    (∀ v m, lookupNatInfo v context.vars = some m → m ≤ context.maxVar) ∧
    (∀ n, live n = true → (tLocals n).isSome) ∧
    ∀ vname v, FLOOKUP sLocals vname = some v →
      ∃ n, lookupNatInfo vname context.vars = some n ∧ live n = true ∧
        tLocals n = some (wlabWloc v)

/-- Untagged iff form of `crepToLoopLocalsRel`, kept for rewriting. -/
theorem crepToLoopLocalsRel_iff {width : Nat} [NeZero width] {α : Type} (context : LoopContext α)
    (live : Nat → Bool)
    (sLocals : FiniteMap Nat (PanWordLab (BitVec width)))
    (tLocals : Nat → Option (LoopValue (BitVec width))) :
    crepToLoopLocalsRel context live sLocals tLocals ↔
      (∀ x y n m,
          lookupNatInfo x context.vars = some n →
          lookupNatInfo y context.vars = some m → n = m → x = y) ∧
        (∀ v m, lookupNatInfo v context.vars = some m → m ≤ context.maxVar) ∧
        (∀ n, live n = true → (tLocals n).isSome) ∧
        (∀ vname v, FLOOKUP sLocals vname = some v →
∃ n, lookupNatInfo vname context.vars = some n ∧ live n = true ∧
        tLocals n = some (wlabWloc v)) :=
  Iff.rfl

/-! ## Finite-map-shaped support for `locals_rel_def`

HOL `crep_to_loop$ctxt` carries `vars : num |-> num` (a finite map), whereas the
production `LoopContext.vars` is a list-backed association list.  The
proof-side carrier below uses the repo's `FiniteMap` (the same rendering of
HOL's `|->` as `PanToCrepProofContext.vars`).  HOL's `sptree$num_set`
(`domain l`, `n ∈ domain l`) is rendered as a Boolean membership map and
`sptree$num_map` (`lookup n t_locals`) as its extensional Option-valued
lookup. The standalone memory/global relations use these renderings over exact
fields; whole-state and context relations stay untagged until their
String-backed code-name carriers are aligned. -/

/-- Proof-side context analogue for Cake's `crep_to_loop` context. Its `vars`
    field uses HOL's finite-map shape, but `funcs` remains keyed by production
    `FunName = String` rather than HOL `mlstring`, so declarations quantifying
    over this whole record remain untagged. -/
structure CrepToLoopFiniteMapContext where
  vars : FiniteMap Nat Nat
  funcs : FiniteMap FunName (Nat × Nat)
  vmax : Nat
  target : Compiler.Encoders.Asm.AsmArchitecture

/-- Flapjack analogue of HOL `crep_to_loop$locals_rel_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:101-111`, withdrawn tag
    `flapjack-dlc.28`), deliberately untagged. HOL states, over a `ctxt` whose
    `vars : num |-> num`, `vmax : num`, `funcs : (mlstring |-> ...)` and
    `target` fields,

      `locals_rel ctxt (l:sptree$num_set) (s_locals:num |-> 'a word_lab)
        t_locals <=> distinct_vars ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\
        domain l ⊆ domain t_locals /\
        !vname v. FLOOKUP s_locals vname = SOME v ==>
          ?n. FLOOKUP ctxt.vars vname = SOME n /\ n ∈ domain l /\
            lookup n t_locals = SOME (wlab_wloc v)`.

    The clause structure matches, but the carriers are only representations:
    `ctxt.funcs : FiniteMap FunName (...)` with `FunName = String` versus HOL
    `mlstring` (this field is ignored by the relation, yet still fixes the
    quantified context's type, so it is a mismatch); `sptree$num_set` `l` with
    `domain l`/`n ∈ domain l` versus the Boolean predicate `live`; `sptree$num_map`
    `t_locals` with `lookup n t_locals` versus the Option-valued function
    `tLocals`; and `'a word_lab` versus `LoopValue (BitVec width)`. The
    `distinct_vars`/`ctxt_max` conjuncts are the parametric Flapjack renderings
    `crepToLoopDistinctVars`/`crepToLoopCtxtMax`. `names_as_string` cannot
    authorize the `num_set`/`num_map`/`word_lab`/`FunName` carriers, and no
    `NameRanged` byte witness applies (`locals_rel` is a `Prop`).

    Direct HOL oracle: `scripts/hol-probes/crep_to_loop_locals_rel_probe.out`
    rows `ctxt_vars_lookup`, `distinct_component`, `ctxt_max_component`,
    `set_domain_mem`, `map_lookup`, `subset_domain_component`; exercised by
    `Flapjack/Test/CrepToLoopParity.lean` (`localsRelContext` and the
    `crepToLoopLocalsRelHOL` examples/fixtures). Faithful exact-carrier port
    tracked by `flapjack-pxn.18.5.6.9.1`. -/
def crepToLoopLocalsRelHOL {width : Nat} [NeZero width]
    (ctxt : CrepToLoopFiniteMapContext)
    (live : Nat → Bool)
    (sLocals : FiniteMap Nat (PanWordLab (BitVec width)))
    (tLocals : Nat → Option (LoopValue (BitVec width))) : Prop :=
  crepToLoopDistinctVars ctxt.vars ∧
  crepToLoopCtxtMax ctxt.vmax ctxt.vars ∧
  (∀ n, live n = true → (tLocals n).isSome) ∧
  ∀ vname v, FLOOKUP sLocals vname = some v →
    ∃ n, FLOOKUP ctxt.vars vname = some n ∧ live n = true ∧
      tLocals n = some (wlabWloc v)

/-- Untagged iff form of `crepToLoopLocalsRelHOL`, kept for rewriting. -/
theorem crepToLoopLocalsRelHOL_iff {width : Nat} [NeZero width]
    (ctxt : CrepToLoopFiniteMapContext)
    (live : Nat → Bool)
    (sLocals : FiniteMap Nat (PanWordLab (BitVec width)))
    (tLocals : Nat → Option (LoopValue (BitVec width))) :
    crepToLoopLocalsRelHOL ctxt live sLocals tLocals ↔
      crepToLoopDistinctVars ctxt.vars ∧
      crepToLoopCtxtMax ctxt.vmax ctxt.vars ∧
      (∀ n, live n = true → (tLocals n).isSome) ∧
      ∀ vname v, FLOOKUP sLocals vname = some v →
        ∃ n, FLOOKUP ctxt.vars vname = some n ∧ live n = true ∧
          tLocals n = some (wlabWloc v) :=
  Iff.rfl

/-! ## `locals_rel` preservation

HOL `locals_rel_insert_gt_vmax` (`crep_to_loopProofScript.sml:228-238`) adds a
fresh `num_map` binding `insert n w lcl'` with `ctxt.vmax < n`; since every
`ctxt.vars` index is `<= ctxt.vmax` (the `ctxt_max` conjunct), the new binding
can never be the target of a source-local obligation, so the relation is
preserved. The `sptree` `insert` is rendered as the function update
`fun m => if m = n then some w else tLocals m`, matching the extensional
`num_map` rendering used by `crepToLoopLocalsRelHOL`. -/

/-- Preservation lemma for the untagged production `locals_rel` analogue,
    corresponding to HOL `locals_rel_insert_gt_vmax`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:228-238`). It retains
    the same context-carrier mismatch and therefore has no HOL tag. -/
theorem crepToLoopLocalsRelHOL_insert_gt_vmax {width : Nat} [NeZero width]
    (ctxt : CrepToLoopFiniteMapContext)
    (live : Nat → Bool)
    (sLocals : FiniteMap Nat (PanWordLab (BitVec width)))
    (tLocals : Nat → Option (LoopValue (BitVec width)))
    (n : Nat) (w : LoopValue (BitVec width))
    (hrel : crepToLoopLocalsRelHOL ctxt live sLocals tLocals)
    (hn : ctxt.vmax < n) :
    crepToLoopLocalsRelHOL ctxt live sLocals
      (fun m => if m = n then some w else tLocals m) := by
  rw [crepToLoopLocalsRelHOL] at hrel ⊢
  obtain ⟨hd, hmax, hdom, hmap⟩ := hrel
  refine ⟨hd, hmax, ?_, ?_⟩
  · intro m hm
    by_cases hmn : m = n
    · simp [hmn]
    · simpa [hmn] using hdom m hm
  · intro vname v hlk
    obtain ⟨m, hvar, hlive, ht⟩ := hmap vname v hlk
    have hle : m ≤ ctxt.vmax := hmax vname m hvar
    have hmn : m ≠ n := by omega
    exact ⟨m, hvar, hlive, by simp [hmn, ht]⟩

/-- Preservation lemma for the untagged production `locals_rel` analogue,
    corresponding to HOL `locals_rel_cutset_prop`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:239-249`). Shrinking
    the live domain preserves the relation, but the context parameter still
    carries String keys where HOL uses `mlstring`, so no HOL tag is attached. -/
theorem crepToLoopLocalsRelHOL_cutset_prop {width : Nat} [NeZero width]
    (ctxt : CrepToLoopFiniteMapContext)
    (live live' : Nat → Bool)
    (sLocals : FiniteMap Nat (PanWordLab (BitVec width)))
    (tLocals tLocals' : Nat → Option (LoopValue (BitVec width)))
    (hrel : crepToLoopLocalsRelHOL ctxt live sLocals tLocals)
    (hrel' : crepToLoopLocalsRelHOL ctxt live' sLocals tLocals')
    (hsub : ∀ n, live n = true → live' n = true) :
    crepToLoopLocalsRelHOL ctxt live sLocals tLocals' := by
  rw [crepToLoopLocalsRelHOL] at hrel hrel' ⊢
  obtain ⟨hd, hmax, _hdom, hmap⟩ := hrel
  obtain ⟨_hd', _hmax', hdom', hmap'⟩ := hrel'
  refine ⟨hd, hmax, ?_, ?_⟩
  · intro n hn
    exact hdom' n (hsub n hn)
  · intro vname v hlk
    obtain ⟨n, hvar, hlive, _ht⟩ := hmap vname v hlk
    obtain ⟨m, hvar', _hlive', ht'⟩ := hmap' vname v hlk
    have hnm : n = m := Option.some.inj (hvar.symm.trans hvar')
    subst hnm
    exact ⟨n, hvar, hlive, ht'⟩

/-! ## Pure-num context lookups

`crep_to_loopScript.sml`'s `find_var`/`find_lab` are plain finite-map lookups
with default `0`; over `CrepToLoopFiniteMapContext` they need no width. -/

/-- Exact port of HOL `find_var_def`
    (`cakeml/pancake/crep_to_loopScript.sml:20-25`). -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "find_var_def"]
def findVarHOL (ctxt : CrepToLoopFiniteMapContext) (v : Nat) : Nat :=
  match FLOOKUP ctxt.vars v with
  | some n => n
  | none => 0

/- FLAPJACK-SPECIFIC (not an exact HOL port): `find_lab_def`
   (`cakeml/pancake/crep_to_loopScript.sml:27-32`) keys `ctxt.funcs` by HOL
   `funname = mlstring`, while `CrepToLoopFiniteMapContext.funcs` is a
   `FiniteMap FunName (Nat × Nat)` with `FunName = String`; the key carrier
   differs even though the lookup/default-0 equations match. HOL's `context`
   record declares `funcs : funname |-> num # num`, with `funname = mlstring`;
   this Lean definition therefore cannot be tagged by matching its equations
   alone. Direct HOL probes cover hit/miss lookup, and Lean parity examples
   exercise this helper, but neither establishes equality of the key carriers.
   The exact counterpart needs an MlString-keyed loop-context carrier
   (dependency `flapjack-pxn.18.3.5.8` / the downstream MlString audit).
   The executed `crepFindLab` is separately tested, not an exact-carrier
   witness for this proof-side helper; no `@[hol]` tag is attached yet. -/
def findLabHOL (ctxt : CrepToLoopFiniteMapContext) (f : FunName) : Nat :=
  match FLOOKUP ctxt.funcs f with
  | some (n, _) => n
  | none => 0

/-! ## Context construction

`crep_to_loopScript.sml`'s `mk_ctxt`/`make_vmap` build the finite-map compiler
context. `make_vmap` has HOL's numeric-key carrier; `mk_ctxt` below still uses
String keys for `funcs`, unlike HOL's `mlstring` keys. -/

/- FLAPJACK-SPECIFIC (not an exact HOL port): `mk_ctxt_def`
   (`cakeml/pancake/crep_to_loopScript.sml:221-228`) takes `funcs` keyed by HOL
   `crepLang$funname = mlstring` (`crepLangScript.sml:21`), while
   `CrepToLoopFiniteMapContext.funcs` is keyed by `FunName = String`; the four
   field assignments match but the input and result carriers differ. The HOL
   probe checks all four projected fields, and Lean examples check analogous
   projections; these tests do not establish carrier equivalence. The exact
   counterpart needs an MlString-keyed loop-context carrier (dependency
   `flapjack-pxn.18.3.5.8` / the downstream MlString audit), so no `@[hol]`
   tag is attached yet. -/
def mkCtxtHOL (target : Compiler.Encoders.Asm.AsmArchitecture) (vmap : FiniteMap Nat Nat)
    (functions : FiniteMap FunName (Nat × Nat)) (vmax : Nat) :
    CrepToLoopFiniteMapContext :=
  { vars := vmap, funcs := functions, vmax := vmax, target := target }

/-- Exact port of HOL `make_vmap_def`
    (`cakeml/pancake/crep_to_loopScript.sml:230-233`): Cake's
    `FEMPTY |++ ZIP (params, GENLIST I (LENGTH params))`. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "make_vmap_def"]
def makeVmapHOL (params : List Nat) : FiniteMap Nat Nat :=
  FUPDATE_LIST FEMPTY (params.zip (List.range params.length))

/-! ## Executable `crepMakeVmap` vs the tagged HOL `make_vmap_def` -/

/-- Adapter from the executable list-backed lookup map to the finite map built
    by replaying the association list in reverse (Cake's `FEMPTY |++ ...`). -/
def natInfoMapToFiniteMap [BEq Nat] (entries : NatInfoMap β) : FiniteMap Nat β :=
  FUPDATE_LIST FEMPTY entries.reverse

theorem FUPDATE_LIST_append_repr [BEq Nat] (fm : FiniteMap Nat β)
    (entries rest : List (Nat × β)) :
    FUPDATE_LIST fm (entries ++ rest) = FUPDATE_LIST (FUPDATE_LIST fm entries) rest := by
  simp [FUPDATE_LIST, List.foldl_append]

/-- Kernel-checked representation theorem: the list-backed first-match
    `lookupNatInfo` and `FLOOKUP` of the reversed replay agree at every key,
    including duplicate names. -/
theorem lookupNatInfo_eq_flookup_natInfoMapToFiniteMap [BEq Nat] [LawfulBEq Nat]
    (name : Nat) (entries : NatInfoMap β) :
    lookupNatInfo name entries = FLOOKUP (natInfoMapToFiniteMap entries) name := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rw [natInfoMapToFiniteMap, List.reverse_cons, FUPDATE_LIST_append_repr,
        FUPDATE_LIST_cons, FUPDATE_LIST_nil, FLOOKUP_update]
      rw [lookupNatInfo]
      by_cases h : entry.1 = name
      · simp [h]
      · simp [h]
        simpa [natInfoMapToFiniteMap] using ih

/-- Faithful production semantics for HOL `make_vmap_def`: the executed
    `crepMakeVmap` replays the positional pairs most-recent-first, so its
    first-match lookup reproduces HOL's last-binding-wins behaviour for a
    duplicate parameter name.  This is the general correspondence with the
    tagged `makeVmapHOL`, valid for every parameter list. -/
theorem lookupNatInfo_crepMakeVmap_eq_flookup_makeVmapHOL (params : List Nat) (name : Nat) :
    lookupNatInfo name (crepMakeVmap params) = FLOOKUP (makeVmapHOL params) name := by
  simp only [crepMakeVmap, makeVmapHOL,
    lookupNatInfo_eq_flookup_natInfoMapToFiniteMap, natInfoMapToFiniteMap,
    List.reverse_reverse]

/-- Exact port of HOL `make_funcs` (`cakeml/pancake/crep_to_loopScript.sml:247`).
    HOL derives, for each program entry `(name, params, body)`,
    `(name, (num, LENGTH params))` where `num = index + first_name`; the result
    is `alist_to_fmap` of that association list. HOL is polymorphic in the
    triple components, so this port keeps `α`, `β`, `γ` polymorphic too; the
    `alist_to_fmap` first-inserted-binding-wins behaviour is rendered as
    `FUPDATE_LIST FEMPTY entries.reverse` (matching the `functionInfosHOL`
    precedent). -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "make_funcs_def"]
def crepToLoopMakeFuncsHOL [BEq α] [LawfulBEq α] {β γ : Type}
    (prog : List (α × List β × γ)) : FiniteMap α (Nat × Nat) :=
  FUPDATE_LIST FEMPTY
    ((prog.zip (List.range prog.length)).map
      (fun entry =>
        (entry.1.1, (firstLoopName + entry.2, entry.1.2.1.length)))).reverse

/-! ## Association-list lookup

`crep_to_loopProofScript.sml`'s `mem_lookup_fromalist_some` (`:3813`) concludes
`lookup n (fromAList xs) = SOME x` for an HOL sptree. The helper below instead
concludes `List.lookup n xs = some x`. Although that is useful for association
lists, it is not the HOL theorem: `fromAList` has not yet been ported. The exact
sptree statement is tracked by bead `flapjack-b0s`. -/

/-- Flapjack-only association-list lemma. It is not HOL's
    `mem_lookup_fromalist_some`, whose conclusion uses sptree `fromAList`. -/
theorem memLookupFromAListSome {β : Type} [BEq Nat] [LawfulBEq Nat]
    {entries : List (Nat × β)} {n : Nat} {x : β}
    (hnodup : (entries.map Prod.fst).Nodup) (hmem : (n, x) ∈ entries) :
    entries.lookup n = some x :=
  list_lookup_of_mem_of_nodup hnodup hmem

/-! ## Association-list map projection

`crep_to_loopProofScript.sml`'s `map_map2_fst` (`:3799`): when two lists have
equal length, projecting the first component of the pointwise `MAP2` that keeps
its first argument recovers the first list.  HOL states this for the concrete
`MAP2` of the program-triple shape `(n, p, b)`; only the projection is
observed, so the wrapped Lean theorem `panMap2_fst_eq` is stated for an
arbitrary second component. -/

/-- Exact port of HOL `map_map2_fst`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3799`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "map_map2_fst"]
theorem mapMap2FstHOL {α β γ : Type} (h : List Nat → β → γ)
    (xs : List α) (ys : List (Nat × List Nat × β))
    (hlen : xs.length = ys.length) :
    (panMap2 (fun x y => (x, List.range y.2.1.length, h y.2.1 y.2.2)) xs ys).map
      Prod.fst = xs :=
  panMap2_fst_eq (fun _ y => (List.range y.2.1.length, h y.2.1 y.2.2)) xs ys hlen

/-! ## Association-list entry agreement

`crep_to_loopProofScript.sml`'s `alookup_el_pair_eq_el` (`:3921`): in a
program association list with distinct first components, the entry at an index
whose first component is `start` and whose parameter list is empty is exactly
the pair recorded by `ALOOKUP prog start`.  The Lean counterpart is the
untagged `getElem_eq_of_lookup_eq` (`Flapjack/Pancake/PanLang.lean`); HOL's
`EL n prog = (start, [], SND (SND (EL n prog)))` premise is rendered literally
as `prog[n] = (start, [], (prog[n]).2.2)` over the right-associated triple. -/

/-- Exact port of HOL `alookup_el_pair_eq_el`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3921`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "alookup_el_pair_eq_el"]
theorem alookupElPairEqEl {α β : Type} [BEq α] [LawfulBEq α]
    (prog : List (α × List Nat × β)) (start : α) (cp : β) (n : Nat)
    (hn : n < prog.length)
    (hshape : prog[n]'hn = (start, [], (prog[n]'hn).2.2))
    (hdistinct : (prog.map Prod.fst).Nodup)
    (hlookup : prog.lookup start = some ([], cp)) :
    prog[n]'hn = (start, [], cp) := by
  have hhead : (prog[n]'hn).1 = start := congrArg Prod.fst hshape
  exact getElem_eq_of_lookup_eq hdistinct hn hhead hlookup

/-! ## Distinctness of `rt_vars` over a distinct map

`crep_to_loopProofScript.sml`'s `all_distinct_ctxt_lookup_all_distinct`
(`:3345`): for a distinct list of return variables and a `distinct_vars`
context, `rt_vars` (the `OPT_MMAP` of `ctxt.vars` over those variables, or
`[n+1]` on failure) is itself `ALL_DISTINCT`. The Lean counterpart uses the
exact carriers `crepToLoopDistinctVars` (`distinct_vars_def`) and `rtVars`
(`rt_vars_def`); `ALL_DISTINCT` is rendered as `List.Nodup`. -/

private theorem forall_some_of_mapM_some {ι : Type} {vars : FiniteMap ι Nat}
    (rts : List ι) (m : List Nat)
    (hm : rts.mapM (fun v => FLOOKUP vars v) = some m) :
    ∀ v ∈ rts, ∃ k, FLOOKUP vars v = some k := by
  induction rts generalizing m with
  | nil => intro v hv; simp at hv
  | cons a l ih =>
      rw [List.mapM_cons] at hm
      cases hfa : FLOOKUP vars a with
      | none => simp [hfa] at hm
      | some k =>
          cases hml : l.mapM (fun v => FLOOKUP vars v) with
          | none => simp [hfa, hml] at hm
          | some m' =>
              intro v hv
              rw [List.mem_cons] at hv
              rcases hv with rfl | hv
              · exact ⟨k, hfa⟩
              · exact ih m' hml v hv

private theorem mem_of_mem_mapM {ι α : Type} {f : ι → Option α}
    (l : List ι) (m : List α) (hm : l.mapM f = some m) :
    ∀ x ∈ m, ∃ b ∈ l, f b = some x := by
  induction l generalizing m with
  | nil => intro x hx; simp at hm; subst hm; simp at hx
  | cons a l ih =>
      intro x hx
      rw [List.mapM_cons] at hm
      cases hfa : f a with
      | none => simp [hfa] at hm
      | some y =>
          cases hml : l.mapM f with
          | none => simp [hfa, hml] at hm
          | some m' =>
              simp [hfa, hml] at hm
              subst hm
              rw [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact ⟨a, List.mem_cons_self, hfa⟩
              · obtain ⟨b, hb, hfb⟩ := ih m' hml x hx
                exact ⟨b, List.mem_cons_of_mem a hb, hfb⟩

private theorem nodup_of_mapM_of_inj {ι α : Type} (f : ι → Option α)
    (l : List ι) (m : List α) (hm : l.mapM f = some m) (hl : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : m.Nodup := by
  induction l generalizing m with
  | nil => simp at hm; subst hm; exact List.nodup_nil
  | cons a l ih =>
      rw [List.mapM_cons] at hm
      cases hfa : f a with
      | none => simp [hfa] at hm
      | some x =>
          cases hml : l.mapM f with
          | none => simp [hfa, hml] at hm
          | some m' =>
              simp [hfa, hml] at hm
              subst hm
              rw [List.nodup_cons] at hl
              obtain ⟨hanot, hl'⟩ := hl
              refine List.nodup_cons.mpr
                ⟨?_, ih m' hml hl' (fun c hc d hd hcd =>
                  hinj c (List.mem_cons_of_mem a hc) d (List.mem_cons_of_mem a hd) hcd)⟩
              intro hxmem
              obtain ⟨b, hb, hfb⟩ := mem_of_mem_mapM l m' hml x hxmem
              have hab : a = b :=
                hinj a (List.mem_cons_self) b (List.mem_cons_of_mem a hb) (hfa.trans hfb.symm)
              exact hanot (hab ▸ hb)

/-- Flapjack analogue of HOL `all_distinct_ctxt_lookup_all_distinct`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3345`). Its context uses
    `FunName = String` as the function-map key, whereas HOL context functions are
    keyed by `mlstring`; the theorem is intentionally untagged until that context
    carrier is exact. -/
theorem allDistinctCtxtLookupAllDistinct (ctxt : CrepToLoopFiniteMapContext)
    (rts : List Nat) (n : Nat)
    (hrts : rts.Nodup) (hinj : crepToLoopDistinctVars ctxt.vars) :
    (rtVars ctxt.vars rts n).Nodup := by
  unfold rtVars
  cases hmap : rts.mapM (fun v => FLOOKUP ctxt.vars v) with
  | none => simp
  | some m =>
      simp only
      refine nodup_of_mapM_of_inj _ rts m hmap hrts (fun a ha b hb hfab => ?_)
      obtain ⟨ka, hka⟩ := forall_some_of_mapM_some rts m hmap a ha
      obtain ⟨kb, hkb⟩ := forall_some_of_mapM_some rts m hmap b hb
      have hk : ka = kb := by
        rw [hka, hkb] at hfab
        exact Option.some.inj hfab
      exact hinj a b ka kb hka hkb hk

/-- Exact port of HOL `list_insert_SNOC`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:386`): inserting the
    snoc'd key list is the same as inserting the tail first and then the final
    key. HOL `SNOC x y` is `y ++ [x]`; `list_insert`/`insert` are the sptree
    operations, rendered here by the exact `Spt` carrier. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "list_insert_SNOC"]
theorem sptListInsert_snoc (x : Nat) (ys : List Nat) (tree : NumSet) :
    sptListInsert (ys ++ [x]) tree = sptInsert x () (sptListInsert ys tree) := by
  induction ys generalizing tree with
  | nil => rfl
  | cons y ys ih => simp [sptListInsert, ih]

/-- Exact port of HOL `insert_insert_eq`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:380`): inserting the
    same key with the same value twice is the same as inserting it once. HOL
    `insert` is the `sptree` operation, rendered here by the exact `Spt`
    carrier with the matching recursive key arithmetic. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "insert_insert_eq"]
theorem sptInsert_insert_eq {α : Type} (a : Nat) (b : α) (tree : Spt α) :
    sptInsert a b (sptInsert a b tree) = sptInsert a b tree := by
  revert b tree
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b tree
    by_cases h0 : a = 0
    · subst h0
      cases tree <;> simp [sptInsert]
    · have ha : 0 < a := Nat.pos_of_ne_zero h0
      have hk : (a - 1) / 2 < a := by
        have hle : (a - 1) / 2 ≤ a - 1 := Nat.div_le_self _ _
        have hlt : a - 1 < a := Nat.sub_lt ha (by decide)
        omega
      by_cases h2 : a % 2 = 0
      · cases tree with
        | ln => rw [sptInsert.eq_1, if_neg h0, if_pos h2, sptInsert.eq_3, if_neg h0, if_pos h2, ih ((a-1)/2) hk b .ln]
        | ls existing => rw [sptInsert.eq_2, if_neg h0, if_pos h2, sptInsert.eq_4, if_neg h0, if_pos h2, ih ((a-1)/2) hk b .ln]
        | bn left right => rw [sptInsert.eq_3, if_neg h0, if_pos h2, sptInsert.eq_3, if_neg h0, if_pos h2, ih ((a-1)/2) hk b left]
        | bs left existing right => rw [sptInsert.eq_4, if_neg h0, if_pos h2, sptInsert.eq_4, if_neg h0, if_pos h2, ih ((a-1)/2) hk b left]
      · cases tree with
        | ln => rw [sptInsert.eq_1, if_neg h0, if_neg h2, sptInsert.eq_3, if_neg h0, if_neg h2, ih ((a-1)/2) hk b .ln]
        | ls existing => rw [sptInsert.eq_2, if_neg h0, if_neg h2, sptInsert.eq_4, if_neg h0, if_neg h2, ih ((a-1)/2) hk b .ln]
        | bn left right => rw [sptInsert.eq_3, if_neg h0, if_neg h2, sptInsert.eq_3, if_neg h0, if_neg h2, ih ((a-1)/2) hk b right]
        | bs left existing right => rw [sptInsert.eq_4, if_neg h0, if_neg h2, sptInsert.eq_4, if_neg h0, if_neg h2, ih ((a-1)/2) hk b right]

/-- Exact port of HOL `list_insert_insert`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:406`): a single `insert`
    under `list_insert` may be moved to the front, provided it keeps the same
    key and unit value. HOL `insert`/`list_insert` are the sptree operations,
    rendered here by the exact `Spt` carrier. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "list_insert_insert"]
theorem sptListInsert_insert (x : Nat) (xs : List Nat) (tree : NumSet) :
    sptInsert x () (sptListInsert xs tree) = sptListInsert xs (sptInsert x () tree) := by
  induction xs generalizing tree with
  | nil => rfl
  | cons y ys ih =>
    simp only [sptListInsert]
    rw [ih (sptInsert y () tree)]
    by_cases hxy : x = y
    · subst hxy
      rfl
    · rw [sptInsert_swap x y () () tree hxy]

/-- Exact port of HOL `list_insert_append`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:414`): inserting a
    concatenated key list equals inserting the two lists in turn. HOL
    `list_insert` is the sptree operation, rendered here by the exact `Spt`
    carrier. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "list_insert_append"]
theorem sptListInsert_append (xs ys : List Nat) (tree : NumSet) :
    sptListInsert (xs ++ ys) tree = sptListInsert xs (sptListInsert ys tree) := by
  induction xs generalizing tree with
  | nil => simp only [List.nil_append, sptListInsert]
  | cons x xs ih =>
    simp only [List.cons_append, sptListInsert]
    rw [ih (sptInsert x () tree), sptListInsert_insert x ys tree]

set_option linter.unusedSimpArgs false in
/-- One byte-store step of `writeBytearrayMemRel`: the pan and loop `mem_store_byte`
    updates preserve the relation on `dom` when the alignments and set-byte
    operations agree.  `smemRec`/`tmemRec` are the recursively written memories
    that the store reads, while `smem0`/`tmem0` are the original memories HOL
    returns when the store fails.  The pan memory is carried on the exact
    `HolWordLab` port; `crepToLoopMemRel` reads it through production `PanWordLab`
    via `HolWordLab.toPanWordLab`. -/
private theorem writeBytearrayMemRel_step {width : Nat} [NeZero width]
    (hdiv : width % 8 = 0) (address : BitVec width) (byte : UInt8)
    (bigEndian : Bool)
    (smemRec : BitVec width → HolWordLab width)
    (tmemRec : BitVec width → LoopValue (BitVec width))
    (smem0 : BitVec width → HolWordLab width)
    (tmem0 : BitVec width → LoopValue (BitVec width))
    (dom : BitVec width → Bool)
    (hrec : crepToLoopMemRel (fun a => (smemRec a).toPanWordLab) tmemRec dom)
    (h0 : crepToLoopMemRel (fun a => (smem0 a).toPanWordLab) tmem0 dom) :
    crepToLoopMemRel
      (fun a => (match panMemStoreByteHOL smemRec (fun a => dom a = true) bigEndian address byte with
        | some updated => updated
        | none => smem0) a |>.toPanWordLab)
      (match memStoreByteAuxHOL tmemRec (fun a => dom a = true) bigEndian address byte with
       | some updated => updated
       | none => tmem0)
      dom := by
  by_cases hdom : dom (panByteAlignHOL (width := width) address) = true
  · cases hsmem : smemRec (panByteAlignHOL (width := width) address) with
    | word cell =>
      have hA : wlabWloc ((smemRec (panByteAlignHOL (width := width) address)).toPanWordLab) =
          tmemRec (panByteAlignHOL (width := width) address) := hrec _ hdom
      rw [hsmem, HolWordLab.toPanWordLab_word, wlabWloc] at hA
      have htmem : tmemRec (panByteAlignHOL (width := width) address) = .word cell := hA.symm
      have hpan : panMemStoreByteHOL smemRec (fun a => dom a = true) bigEndian address byte =
          some (fun current => if current = panByteAlignHOL (width := width) address
            then .word (panSetByteHOL address (BitVec.ofNat width byte.toNat) cell bigEndian)
            else smemRec current) := by
        simp only [panMemStoreByteHOL, hsmem, if_pos hdom]
      have htgt : memStoreByteAuxHOL tmemRec (fun a => dom a = true) bigEndian address byte =
          some (fun current => if current = panByteAlignHOL (width := width) address
            then .word (riscvSetByteHOL bigEndian address cell byte)
            else tmemRec current) := by
        have halign : riscvByteAlignHOL address = panByteAlignHOL (width := width) address :=
          riscvByteAlignHOL_eq_panByteAlignHOL address
        simp only [memStoreByteAuxHOL, halign, htmem, if_pos hdom]
      rw [hpan, htgt]
      dsimp only
      intro ad had
      by_cases hcur : ad = panByteAlignHOL (width := width) address
      · subst hcur
        simp only [if_pos rfl, HolWordLab.toPanWordLab_word, wlabWloc]
        exact congrArg LoopValue.word
          (panSetByteHOL_eq_riscvSetByteHOL hdiv address cell byte bigEndian)
      · simp only [if_neg hcur]
        exact hrec ad had
  · have hpan : panMemStoreByteHOL smemRec (fun a => dom a = true) bigEndian address byte = none := by
      cases hsmem : smemRec (panByteAlignHOL (width := width) address) with
      | word cell => simp only [panMemStoreByteHOL, hsmem, if_neg hdom]
    have htgt : memStoreByteAuxHOL tmemRec (fun a => dom a = true) bigEndian address byte = none := by
      have halign : riscvByteAlignHOL address = panByteAlignHOL (width := width) address :=
        riscvByteAlignHOL_eq_panByteAlignHOL address
      simp only [memStoreByteAuxHOL, halign]
      cases htm : tmemRec (panByteAlignHOL (width := width) address) with
      | word v => simp only [htm, if_neg hdom]
      | loc i o => simp only [htm]
    rw [hpan, htgt]
    dsimp only
    exact h0

set_option linter.unusedSimpArgs false in
/-- Flapjack-specific restatement of HOL `write_bytearray_mem_rel`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:251-256`): writing the
    same byte array to two `mem_rel`-related memories keeps them related on the
    same domain. The source `panSem$write_bytearray` (`panWriteBytearrayHOL`)
    and target `wordSem$write_bytearray` (`writeBytearrayHOL`) are the
    total-function renderings, `dom` is HOL's address set as a `Bool` predicate,
    and the two `mem_store_byte` steps agree through
    `riscvByteAlignHOL_eq_panByteAlignHOL` and
    `panSetByteHOL_eq_riscvSetByteHOL`. The pan memory is the exact `HolWordLab`
    `panSem$word_lab` carrier, read through production `PanWordLab` via
    `HolWordLab.toPanWordLab` (the kernel-checked isomorphism).
    The HOL tag is withdrawn (bead flapjack-pxn.18.5.6.17.1; coordinator HOLD
    2026-09-26): the HOL theorem has no width-divisibility premise, while `hdiv`
    (`width % 8 = 0`) is needed here because the two byte-codec renderings
    coincide only when `8 ∣ width`; compiler word widths 32/64 do not make the
    unrestricted HOL theorem exact. A faithful port needs width-free byte
    renderings or a HOL-derived divisibility argument, tracked by a prerequisite
    bead. -/
theorem writeBytearrayMemRel {width : Nat} [NeZero width] (hdiv : width % 8 = 0)
    (smem : BitVec width → HolWordLab width)
    (tmem : BitVec width → LoopValue (BitVec width))
    (dom : BitVec width → Bool)
    (bytes : List UInt8) (address : BitVec width) (bigEndian : Bool) :
    crepToLoopMemRel (fun a => (smem a).toPanWordLab) tmem dom →
    crepToLoopMemRel
      (fun a => (panWriteBytearrayHOL address bytes smem (fun a => dom a = true) bigEndian a).toPanWordLab)
      (writeBytearrayHOL address bytes tmem (fun a => dom a = true) bigEndian)
      dom := by
  revert address
  induction bytes with
  | nil =>
      intro address h
      simpa only [panWriteBytearrayHOL, writeBytearrayHOL] using h
  | cons byte rest ih =>
      intro address h
      simp only [panWriteBytearrayHOL, writeBytearrayHOL]
      exact writeBytearrayMemRel_step hdiv address byte bigEndian
        (panWriteBytearrayHOL (address + 1) rest smem (fun a => dom a = true) bigEndian)
        (writeBytearrayHOL (address + 1) rest tmem (fun a => dom a = true) bigEndian)
        smem tmem dom (ih (address + 1) h) h

end Flapjack
