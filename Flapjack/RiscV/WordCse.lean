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

structure WordCseState where
  currHeap : Option Nat

def wordCseEmpty : WordCseState := { currHeap := none }

def wordCseLookup (state : WordCseState) (store : WordStore α) : Option Nat :=
  match store with
  | .currHeap => state.currHeap
  | _ => none

def wordCseUpdate (state : WordCseState) (store : WordStore α)
    (name : Nat) : WordCseState :=
  match store with
  | .currHeap => { currHeap := some name }
  | _ => state

def wordCseClearStore (state : WordCseState) (store : WordStore α) : WordCseState :=
  match store with
  | .currHeap => wordCseEmpty
  | _ => state

def wordCseProg : WordCseState → WordProg α → WordProg α × WordCseState
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
  | state, .set store value =>
      (.set store value, wordCseClearStore state store)
  | state, .inst instruction => (.inst instruction, state)
  | state, .call returns target arguments handler =>
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
        if thenState.currHeap = elseState.currHeap then thenState else wordCseEmpty)
  | state, .shareInst operator name address =>
      (.shareInst operator name address, state)
  | state, program => (program, state)
termination_by _ program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordCseProp (program : WordProg α) : WordProg α :=
  (wordCseProg wordCseEmpty program).1

end Flapjack.RiscV
