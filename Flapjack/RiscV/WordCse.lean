import Flapjack.Word

/-!
# Small Word common-subexpression boundary

Cake's `word_cse` records repeated `Get` reads and replaces a later read of
the same store with a move.  This is the first stateful CSE fact needed by the
RISC-V artifact path: repeated `CurrHeap` reads otherwise create an extra
value and prevent the following `word_copy` pass from coalescing the source
names.  Other CSE facts remain explicit future work.
-/

namespace Flapjack.RiscV

open Flapjack

variable {α : Type u} [BEq α]

structure WordCseState (α : Type u) [BEq α] where
  currHeap : Option Nat
  constants : List (α × Nat)

def wordCseEmpty : WordCseState α := { currHeap := none, constants := [] }

def wordCseLookup (state : WordCseState α) (store : WordStore α) : Option Nat :=
  match store with
  | .currHeap => state.currHeap
  | _ => none

def wordCseUpdate (state : WordCseState α) (store : WordStore α)
    (name : Nat) : WordCseState α :=
  match store with
  | .currHeap => { state with currHeap := some name }
  | _ => state

def wordCseLookupConst (state : WordCseState α) (value : α) : Option Nat :=
  state.constants.find? (fun entry => entry.1 == value) |>.map Prod.snd

def wordCseRememberConst (state : WordCseState α) (value : α) (name : Nat) :
    WordCseState α :=
  { state with constants := (value, name) ::
      state.constants.filter (fun entry => entry.1 != value) }

def wordCseClearDestination (state : WordCseState α) (name : Nat) :
    WordCseState α :=
  { state with constants := state.constants.filter (fun entry => entry.2 != name) }

def wordCseClearStore (state : WordCseState α) (store : WordStore α) :
    WordCseState α :=
  match store with
  | .currHeap => { state with currHeap := none }
  | _ => state

def wordCseProg : WordCseState α → WordProg α → WordProg α × WordCseState α
  | state, .skip => (.skip, state)
  | state, .seq first second =>
      let (first, state) := wordCseProg state first
      let (second, state) := wordCseProg state second
      (.seq first second, state)
  | state, .get destination store =>
      match wordCseLookup state store with
      | some source => (.move 1 [(destination, source)],
          wordCseUpdate state store destination)
      | none => (.get destination store,
          wordCseUpdate state store destination)
  | state, .assign destination (.lookup store) =>
      match wordCseLookup state store with
      | some source => (.move 1 [(destination, source)],
          wordCseUpdate state store destination)
      | none => (.assign destination (.lookup store),
          wordCseUpdate state store destination)
  | state, .assign destination (.const value) =>
      match wordCseLookupConst state value with
      | some source => (.move 0 [(destination, source)],
          wordCseClearDestination state destination)
      | none => (.assign destination (.const value),
          wordCseRememberConst (wordCseClearDestination state destination)
            value destination)
  | state, .assign destination value =>
      (.assign destination value, wordCseClearDestination state destination)
  | state, .set store value =>
      (.set store value, wordCseClearStore state store)
  | state, .inst instruction => (.inst instruction, state)
  | _state, .call returns target arguments handler =>
      (.call returns target arguments handler, wordCseEmpty)
  | state, .loop liveIn body liveOut =>
      let (body, _) := wordCseProg wordCseEmpty body
      (.loop liveIn body liveOut, wordCseEmpty)
  | state, .mustTerminate body =>
      let (body, state) := wordCseProg state body
      (.mustTerminate body, state)
  | state, .ite operator condition right thenBranch elseBranch =>
      let (thenBranch, thenState) := wordCseProg state thenBranch
      let (elseBranch, elseState) := wordCseProg state elseBranch
      (.ite operator condition right thenBranch elseBranch,
        if thenState.currHeap = elseState.currHeap then
          { currHeap := thenState.currHeap, constants := [] }
        else wordCseEmpty)
  | state, .shareInst operator name address =>
      (.shareInst operator name address, state)
  | state, program => (program, state)
termination_by _ program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordCseProp (program : WordProg α) : WordProg α :=
  (wordCseProg wordCseEmpty program).1

end Flapjack.RiscV
