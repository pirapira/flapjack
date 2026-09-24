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

Tagged declarations that compare word-typed state fields are width-specialized
to `BitVec width`, because HOL `crepSem$state`/`loopSem$state` are word-length
indexed (`'a word` fields) and a generic-`α` carrier would not be an exact
counterpart; those declarations carry `[NeZero width]`, because HOL word types
have positive `dimindex` while `BitVec 0` is inhabited and has no HOL
counterpart.  The relations over pure `num`/`num` finite maps (`distinct_funcs`,
`distinct_vars`, `ctxt_max`) are polymorphic exactly as the un-annotated HOL
`Definition`s infer them (key, and value where no arithmetic constrains it).
-/

namespace Flapjack

/-- Exact port of HOL `state_rel_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:28-36`):
    `state_rel s t` holds when the source and target states agree on the
    memory/stack domains, clock, endianness, FFI state, and base/top addresses.
    The remaining `CrepHolState` fields (`locals`, `globals`, `code`, `memory`)
    are related separately by `locals_rel`/`code_rel`/`mem_rel`/`globals_rel`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "state_rel_def"]
def crepToLoopStateRel {width : Nat} [NeZero width] {σ : Type} (s : CrepHolState (BitVec width) σ)
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

/-- Exact port of HOL `state_rel_clock_add_zero`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:219-223`): a state
    relation is preserved when the target clock is advanced by zero. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "state_rel_clock_add_zero"]
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

/-! ## `locals_rel` (UNTTAGGED — carrier gap)

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

The exact tagged port is `crepToLoopLocalsRelHOL` below over the finite-map
`CrepToLoopFiniteMapContext` carrier (`sptree$num_set`/`num_map` rendered
extensionally); this untagged rendering over the production list-backed
`LoopContext` is kept for production-side clients. -/

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

/-! ## Exact carriers for `locals_rel_def`

HOL `crep_to_loop$ctxt` carries `vars : num |-> num` (a finite map), whereas the
production `LoopContext.vars` is a list-backed association list.  The
proof-side carrier below uses the repo's `FiniteMap` (the same rendering of
HOL's `|->` as `PanToCrepProofContext.vars`).  HOL's `sptree$num_set`
(`domain l`, `n ∈ domain l`) is rendered as a Boolean membership map and
`sptree$num_map` (`lookup n t_locals`) as its extensional Option-valued
lookup — the same set-as-membership-map / finite-map-as-function renderings
already accepted for the tagged `crepToLoopStateRel`, `crepToLoopMemRel` and
`crepToLoopGlobalsRel`. -/

/-- Proof-side carrier for Cake's `crep_to_loop` context, with HOL's finite-map
    `vars : num |-> num`; field names mirror the HOL record. -/
structure CrepToLoopFiniteMapContext where
  vars : FiniteMap Nat Nat
  funcs : FiniteMap FunName (Nat × Nat)
  vmax : Nat
  target : RiscV.Architecture

/-- Exact width-indexed port of HOL `locals_rel_def`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:101-111`) over the
    finite-map context carrier.  The `sptree$num_set`/`num_map` arguments are
    rendered extensionally (Boolean membership map and Option-valued lookup). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "locals_rel_def"]
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

end Flapjack
