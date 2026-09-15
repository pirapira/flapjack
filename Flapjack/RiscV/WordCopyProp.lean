import Flapjack.RiscV.Allocator

/-!
# Cake-shaped Word copy propagation

Cake runs `word_copy$copy_prop` after SSA and before `three_to_two_reg` and
`word_unreach`.  The allocator boundary used to omit that pass, which leaves
copy-only SSA names live into colouring and changes the exact RISC-V artifact.
This port keeps the source pass's important contract: only allocatable names
are placed in equivalence classes, copies remain in the program, and every
non-copy write invalidates the relevant class.
-/

namespace Flapjack.RiscV

open Flapjack

structure WordCopyState where
  aliases : NatInfoMap Nat
  deriving Repr

def wordCopyEmpty : WordCopyState := { aliases := [] }

def wordCopyLookup (state : WordCopyState) (name : Nat) : Nat :=
  (lookupNatInfo name state.aliases).getD name

def wordCopyUpdate (aliases : NatInfoMap Nat) (name value : Nat) : NatInfoMap Nat :=
  (name, value) :: aliases.filter (fun entry => entry.1 != name)

def wordCopyIsAlloc (name : Nat) : Bool := name % 4 == 1

def wordCopyRemove (state : WordCopyState) (name : Nat) : WordCopyState :=
  if (lookupNatInfo name state.aliases).isSome then wordCopyEmpty else state

def wordCopySet (state : WordCopyState) (destination source : Nat) : WordCopyState :=
  if wordCopyIsAlloc destination && wordCopyIsAlloc source then
    { aliases := wordCopyUpdate state.aliases destination
        (wordCopyLookup state source) }
  else state

def wordCopyExp (state : WordCopyState) : WordExp α → WordExp α
  | .const value => .const value
  | .var name => .var (wordCopyLookup state name)
  | .lookup store => .lookup store
  | .load address => .load (wordCopyExp state address)
  | .op operator arguments => .op operator (arguments.map (wordCopyExp state))
  | .shift operator left right =>
      .shift operator (wordCopyExp state left) (wordCopyExp state right)
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordCopyRegImm (state : WordCopyState) : WordRegImm α → WordRegImm α
  | .imm value => .imm value
  | .reg name => .reg (wordCopyLookup state name)

def wordCopyInst {α : Type u} (state : WordCopyState) : WordInst α → WordInst α × WordCopyState
  | .arith operation =>
      match operation with
      | .longMul left right sourceLeft sourceRight =>
          (.arith (.longMul left right (wordCopyLookup state sourceLeft)
            (wordCopyLookup state sourceRight)),
            wordCopyRemove (wordCopyRemove state left) right)
      | .longDiv left right sourceLeft sourceRight quotient =>
          (.arith (.longDiv left right (wordCopyLookup state sourceLeft)
            (wordCopyLookup state sourceRight) (wordCopyLookup state quotient)),
            wordCopyRemove (wordCopyRemove state left) right)
      | .addCarry destination carry sourceLeft sourceRight carryIn =>
          (.arith (.addCarry destination carry (wordCopyLookup state sourceLeft)
            (wordCopyLookup state sourceRight) (wordCopyLookup state carryIn)),
            wordCopyRemove (wordCopyRemove state destination) carry)
      | .cakeAddCarry destination sourceLeft sourceRight carry =>
          (.arith (.cakeAddCarry destination (wordCopyLookup state sourceLeft)
            (wordCopyLookup state sourceRight) (wordCopyLookup state carry)),
            wordCopyRemove (wordCopyRemove state destination) carry)
      | .div destination dividend divisor =>
          (.arith (.div destination (wordCopyLookup state dividend)
            (wordCopyLookup state divisor)), wordCopyRemove state destination)
  | .mem operator destination address =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          (.mem operator destination (wordCopyLookup state address),
            wordCopyRemove state destination)
      | .store | .store8 | .store16 | .store32 =>
          (.mem operator (wordCopyLookup state destination)
            (wordCopyLookup state address), state)
  | .const destination value =>
      (.const destination value, wordCopyRemove state destination)
  | .binop operator destination source right =>
      match right with
      | .imm value =>
          (.binop operator destination (wordCopyLookup state source) (.imm value),
            wordCopyRemove state destination)
      | .reg name =>
          (.binop operator destination (wordCopyLookup state source)
            (.reg (wordCopyLookup state name)),
            wordCopyRemove state destination)
  | .shiftInst operator destination source amount =>
      match amount with
      | .imm value =>
          (.shiftInst operator destination (wordCopyLookup state source)
            (.imm value),
            wordCopyRemove state destination)
      | .reg name =>
          (.shiftInst operator destination (wordCopyLookup state source)
            (.reg (wordCopyLookup state name)),
            wordCopyRemove state destination)
  | .memOffset operator destination base offset =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          (.memOffset operator destination (wordCopyLookup state base) offset,
            wordCopyRemove state destination)
      | .store | .store8 | .store16 | .store32 =>
          (.memOffset operator (wordCopyLookup state destination)
            (wordCopyLookup state base) offset, state)

def wordCopyMerge (left right : WordCopyState) : WordCopyState :=
  { aliases := left.aliases.filter (fun entry =>
      lookupNatInfo entry.1 right.aliases == some entry.2) }

def wordCopyMoves : WordCopyState → List (Nat × Nat) →
    List (Nat × Nat) × WordCopyState
  | state, [] => ([], state)
  | state, move :: moves =>
      let source := wordCopyLookup state move.2
      let (rewritten, state) := wordCopyMoves state moves
      let state := wordCopySet (wordCopyRemove state move.1) move.1 move.2
      ((move.1, source) :: rewritten, state)
termination_by _ moves => sizeOf moves
decreasing_by all_goals decreasing_trivial

def wordCopyShareExp (state : WordCopyState) : WordExp α → WordExp α
  | .var name => .var (wordCopyLookup state name)
  | .op .add [.var name, .const value] =>
      .op .add [.var (wordCopyLookup state name), .const value]
  | expression => expression

def wordCopyProg : WordCopyState → WordProg α → WordProg α × WordCopyState
  | state, .skip => (.skip, state)
  | state, .move priority moves =>
      let destinations := moves.map Prod.fst
      let sources := moves.map Prod.snd
      if destinations.any (fun name => name ∈ sources) then
        (.move priority moves, wordCopyEmpty)
      else
        let (moves, state) := wordCopyMoves state moves
        (.move priority moves, state)
  | state, .assign destination value =>
      (.assign destination (wordCopyExp state value), wordCopyRemove state destination)
  | state, .inst instruction =>
      let (instruction, state) := wordCopyInst state instruction
      (.inst instruction, state)
  | state, .get destination store =>
      (.get destination store, wordCopyRemove state destination)
  | state, .store address value =>
      (.store (wordCopyExp state address) (wordCopyLookup state value), state)
  | state, .set store value =>
      (.set store (wordCopyExp state value), wordCopyEmpty)
  | state, .seq first second =>
      let (first, state) := wordCopyProg state first
      let (second, state) := wordCopyProg state second
      (.seq first second, state)
  | state, .ite operator condition right thenBranch elseBranch =>
      let (thenBranch, thenState) := wordCopyProg state thenBranch
      let (elseBranch, elseState) := wordCopyProg state elseBranch
      (.ite operator (wordCopyLookup state condition)
          (wordCopyRegImm state right) thenBranch elseBranch,
        wordCopyMerge thenState elseState)
  | state, .loop liveIn body liveOut =>
      let (body, _) := wordCopyProg wordCopyEmpty body
      (.loop liveIn body liveOut, state)
  | state, .mustTerminate body =>
      let (body, state) := wordCopyProg state body
      (.mustTerminate body, state)
  | state, .raise exception => (.raise (wordCopyLookup state exception), state)
  | state, .return label values =>
      (.return label (values.map (wordCopyLookup state)), state)
  | state, .tick => (.tick, state)
  | state, .locValue destination source =>
      (.locValue destination source, wordCopyRemove state destination)
  | _state, .call returns target arguments handler =>
      (.call returns target arguments handler, wordCopyEmpty)
  | state, .shareInst operator name address =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          (.shareInst operator name (wordCopyShareExp state address),
            wordCopyRemove state name)
      | .store | .store8 | .store16 | .store32 =>
          (.shareInst operator name
            (wordCopyShareExp state address), state)
  | state, .break label => (.break label, state)
  | state, .continue label => (.continue label, state)
  | _state, program => (program, wordCopyEmpty)
termination_by _ program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordCopyProp (program : WordProg α) : WordProg α :=
  (wordCopyProg wordCopyEmpty program).1

end Flapjack.RiscV
