import Flapjack.LoopGetVarImm
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.WordLang

/-!
# Exact HOL `loopSem$state` carrier

Counterpart of the `state` datatype in
`cakeml/pancake/semantics/loopSemScript.sml:13-27`:

```
state =
  <| locals  : ('a word_loc) num_map
   ; globals : 5 word  |-> 'a word_loc
   ; memory  : 'a word -> 'a word_loc
   ; mdomain : ('a word) set
   ; sh_mdomain : ('a word) set
   ; clock   : num
   ; code    : (num list # ('a loopLang$prog)) num_map
   ; be      : bool
   ; ffi     : 'ffi ffi_state
   ; base_addr   : 'a word
   ; top_addr    : 'a word |>
```

`LoopSemState` mirrors this field-for-field, width-indexed by the actual word
width (HOL's `'a`, which is nonzero).  The `num_map`/`5 word |-> _` fields use
`FiniteMap` (our `α → Option β` model, with lookup as application, matching the
`sptree$lookup`/`FLOOKUP` behaviour used by the existing ports); `memory` is the
source's *total* function.  `mdomain`/`sh_mdomain` are `W → Bool`, matching HOL
`set` (an `'a -> bool` predicate).

This carrier is deliberately UNTAGGED: the `code` field carries our
`LoopProg (BitVec width)` and the `ffi` field our `FfiState F`, whose exact
source shapes are tracked separately (see the `mlstring`/program-carrier and
`ffi_state` beads).  Only once those sub-carriers are exact may the `state`
datatype itself carry an `@[hol ... "state"]` tag.  The point of this module is
to give `loopSem`-level statements (such as `get_var_imm_def`) a full-state
argument whose map/memory/domain/address fields are already source-shaped, plus
a checked bridge to the production `LoopMachineState`.
-/

namespace Flapjack

/-- `'a word_loc → 'a loopSem` value conversion, which is the identity on the
    payload: `Word w ↦ Word w` and `Loc n m ↦ Loc n m`. -/
def loopValueOfWordLocW {width : Nat} [NeZero width] :
    WordLocW width → LoopValue (BitVec width)
  | .word value => .word value
  | .loc identifier offset => .loc identifier offset

/-- Exact HOL `loopSem$state` (`loopSemScript.sml:13-27`), width-indexed by the
    nonzero word width.  See the module note for the two sub-carriers that are
    not yet source-exact and therefore keep the datatype untagged. -/
structure LoopSemState (width : Nat) [NeZero width] (F : Type) where
  locals : FiniteMap Nat (WordLocW width)
  globals : FiniteMap (BitVec 5) (WordLocW width)
  memory : BitVec width → WordLocW width
  mdomain : BitVec width → Bool
  shMdomain : BitVec width → Bool
  clock : Nat
  code : FiniteMap Nat (List Nat × LoopProg (BitVec width))
  be : Bool
  ffi : FfiState F
  baseAddr : BitVec width
  topAddr : BitVec width

/-- Observational bridge from the exact `LoopSemState` to the production
    `LoopMachineState`.  The word-location payloads are compared through
    `loopValueOfWordLocW`; the total `memory` is option-valued on the
    production side (always present); the address sets are Bool predicates on
    both sides; the code table is related by the production association list
    enumerating entries of the exact finite map (`num_map` has no enumeration
    order, so the source map may contain further entries). -/
def LoopMachineStateRel {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemState width F) (m : LoopMachineState (BitVec width) F) : Prop :=
  (∀ name, m.locals name = (s.locals name).map loopValueOfWordLocW) ∧
  (∀ global, m.globals global = (s.globals global).map loopValueOfWordLocW) ∧
  (∀ address, m.memory address = some (loopValueOfWordLocW (s.memory address))) ∧
  m.mdomain = s.mdomain ∧
  m.shMdomain = s.shMdomain ∧
  m.clock = s.clock ∧
  m.be = s.be ∧
  m.ffi = s.ffi ∧
  m.baseAddr = s.baseAddr ∧
  m.topAddr = s.topAddr ∧
  (∀ entry, entry ∈ m.code → s.code entry.1 = some (entry.2.1, entry.2.2))

/-- Register reads through `get_var_imm` on the production state agree with the
    exact carrier's local lookup under the bridge. -/
theorem getVarImm_reg_eq_of_loopMachineStateRel {width : Nat} [NeZero width]
    {F : Type} {s : LoopSemState width F} {m : LoopMachineState (BitVec width) F}
    (h : LoopMachineStateRel s m) (name : Nat) :
    getVarImm m (.reg name) = (s.locals name).map loopValueOfWordLocW := by
  rw [getVarImm_reg]
  exact h.1 name

/-- Immediate reads are unchanged by the bridge. -/
theorem getVarImm_imm_eq_of_loopMachineStateRel {width : Nat} [NeZero width]
    {F : Type} {s : LoopSemState width F} {m : LoopMachineState (BitVec width) F}
    (_h : LoopMachineStateRel s m) (value : BitVec width) :
    getVarImm m (.imm value) = some (.word value) :=
  getVarImm_imm m value

/-! ## Carrier-level `get_var_imm` / `get_vars`

`get_var_imm_def` (`loopSemScript.sml:165-167`) and `get_vars_def`
(`loopSemScript.sml:98-107`) read only the `locals` finite map.  The defs below
are the exact source recursion expressed directly on `LoopSemState`, so
statement-level ports can be phrased over the source-shaped carrier; they are
UNTAGGED for the same reason the carrier is (see the module note), and are
intended to be retagged together with the carrier once `code`/`ffi` are exact.
-/

namespace LoopSemState

/-- Exact `get_var_imm_def` (`loopSemScript.sml:165-167`), operand first as in
    HOL.  Untagged: the carrier is not yet source-exact. -/
def getVarImm {width : Nat} [NeZero width] {F : Type}
    (operand : RegImm (BitVec width)) (s : LoopSemState width F) :
    Option (WordLocW width) :=
  match operand with
  | .reg name => s.locals name
  | .imm value => some (.word value)

@[simp] theorem getVarImm_reg {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemState width F) (name : Nat) :
    getVarImm (.reg name) s = s.locals name := rfl

@[simp] theorem getVarImm_imm {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemState width F) (value : BitVec width) :
    getVarImm (.imm value) s = some (.word value) := rfl

/-- `get_var_imm` ignores the clock, the loopProps clock-reduction fact. -/
theorem getVarImm_clock {width : Nat} [NeZero width] {F : Type}
    (operand : RegImm (BitVec width)) (s : LoopSemState width F) (ck : Nat) :
    getVarImm operand { s with clock := ck } = getVarImm operand s := by
  cases operand <;> rfl

/-- Exact `get_vars_def` (`loopSemScript.sml:98-107`), state second as in HOL.
    Untagged: the carrier is not yet source-exact. -/
def getVars {width : Nat} [NeZero width] {F : Type} :
    List Nat → LoopSemState width F → Option (List (WordLocW width))
  | [], _ => some []
  | name :: names, s =>
      (s.locals name).bind
        (fun value => (getVars names s).map (fun values => value :: values))

@[simp] theorem getVars_nil {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemState width F) :
    getVars [] s = some [] := rfl

theorem getVars_cons {width : Nat} [NeZero width] {F : Type}
    (name : Nat) (names : List Nat) (s : LoopSemState width F) :
    getVars (name :: names) s =
      (s.locals name).bind
        (fun value => (getVars names s).map (fun values => value :: values)) :=
  rfl

/-- `get_vars` ignores the clock, the loopProps clock-reduction fact. -/
theorem getVars_clock {width : Nat} [NeZero width] {F : Type}
    (names : List Nat) (s : LoopSemState width F) (ck : Nat) :
    getVars names { s with clock := ck } = getVars names s := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp only [getVars]
      rw [ih]

/-- The exact carrier's `get_var_imm` maps to the production `get_var_imm`
    through `loopValueOfWordLocW` under the state bridge. -/
theorem getVarImm_map_eq_of_loopMachineStateRel {width : Nat} [NeZero width]
    {F : Type} {s : LoopSemState width F} {m : LoopMachineState (BitVec width) F}
    (h : LoopMachineStateRel s m) (operand : RegImm (BitVec width)) :
    (getVarImm operand s).map loopValueOfWordLocW = Flapjack.getVarImm m operand := by
  cases operand with
  | reg name => simp only [getVarImm_reg, Flapjack.getVarImm_reg, h.1 name]
  | imm value => rfl

end LoopSemState

end Flapjack