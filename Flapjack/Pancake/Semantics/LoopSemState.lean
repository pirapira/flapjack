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

end Flapjack