import Flapjack.RiscV.Allocator
import Flapjack.RiscV.WordCse

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
  /- `store_to_eq` (`word_copyScript.sml:40`): the equivalence class known to
     hold the value a store currently contains.  Cake keeps an internal class
     number here and resolves it through `from_eq`; the flattened port
     representation already stores the visible representative, so this map
     holds that representative directly. -/
  storeToEq : NatInfoMap Nat
  deriving Repr

def wordCopyEmpty : WordCopyState := { aliases := [], storeToEq := [] }

def wordCopyLookup (state : WordCopyState) (name : Nat) : Nat :=
  (lookupNatInfo name state.aliases).getD name

def wordCopyUpdate (aliases : NatInfoMap Nat) (name value : Nat) : NatInfoMap Nat :=
  (name, value) :: aliases.filter (fun entry => entry.1 != name)

def wordCopyIsAlloc (name : Nat) : Bool := name % 4 == 1

def wordCopyRemove (state : WordCopyState) (name : Nat) : WordCopyState :=
  if (lookupNatInfo name state.aliases).isSome then wordCopyEmpty else state

/-! `set_eq` (`word_copyScript.sml:204-225`).  Cake's equivalence class is
    represented by the *destination* of the copy: `set_eq cs x y` inserts `x`
    (the destination) as the class of `y` (the source) and makes `x` the
    representative, so later uses of the *source* become `x` while uses of `x`
    stay.  The RISC-V oracle (`copy_prop_prog (Seq (Move 0 [(37,25)])
    (Inst (Mem Store 33 (Addr 37 0)))) empty_eq`) keeps `Addr 37` and rewrites
    a later `25` to `37`, which is what the allocator then coalesces. -/
def wordCopySet (state : WordCopyState) (destination source : Nat) : WordCopyState :=
  if wordCopyIsAlloc destination && wordCopyIsAlloc source then
    /- `wordCopyRemove` has already dropped the state when `destination` had a
       class, so `destination` is its own representative here. -/
    let sourceClass := wordCopyLookup state source
    let others := state.aliases.filter (fun entry =>
      entry.1 != destination && entry.1 != source)
    { state with
      aliases := (destination, destination) ::
        (source, destination) ::
        others.map (fun entry =>
          if entry.2 == sourceClass then (entry.1, destination) else entry) }
  else state

/- `lookup_store_eq` (`word_copyScript.sml:252-260`).  Cake resolves the
    recorded internal class through `from_eq` and reports nothing when that
    class no longer exists; the port's representative is live exactly when the
    alias map still carries it. -/
def wordCopyLookupStoreEq (state : WordCopyState) (store : Nat) : Option Nat :=
  match lookupNatInfo store state.storeToEq with
  | none => none
  | some representative =>
      if (lookupNatInfo representative state.aliases).isSome then
        some representative
      else none

/-! `set_store_eq` (`word_copyScript.sml:233-250`).  The SSA invariant makes
    the source an allocatable name, so a name without a class gets its own
    singleton class and a name with one reuses it. -/
def wordCopySetStoreEq (state : WordCopyState) (store name : Nat) : WordCopyState :=
  if wordCopyIsAlloc name then
    match lookupNatInfo name state.aliases with
    | some representative =>
        { state with
          storeToEq := (store, representative) ::
            state.storeToEq.filter (fun entry => entry.1 != store) }
    | none =>
        { aliases := (name, name) ::
            state.aliases.filter (fun entry => entry.1 != name),
          storeToEq := (store, name) ::
            state.storeToEq.filter (fun entry => entry.1 != store) }
  else wordCopyEmpty

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

def wordCopyInst {α : Type} (state : WordCopyState) :
    WordInst α → WordInst α × WordCopyState
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
      | .binOp operator destination sourceLeft sourceRight =>
          let sourceLeft := wordCopyLookup state sourceLeft
          let sourceRight' := wordCopyRegImm state sourceRight
          let sourceRight :=
            match sourceRight' with
            | .reg register =>
                if register = destination then sourceRight else sourceRight'
            | .imm _ => sourceRight'
          (.arith (.binOp operator destination sourceLeft sourceRight),
            wordCopyRemove state destination)
      | .shift operator destination sourceLeft sourceRight =>
          let sourceLeft := wordCopyLookup state sourceLeft
          let sourceRight' := wordCopyRegImm state sourceRight
          let sourceRight :=
            match sourceRight' with
            | .reg register =>
                if register = destination then sourceRight else sourceRight'
            | .imm _ => sourceRight'
          (.arith (.shift operator destination sourceLeft sourceRight),
            wordCopyRemove state destination)
  | .const destination value =>
      (.const destination value, wordCopyRemove state destination)
  | .mem operator destination address =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          (.mem operator destination (wordCopyLookup state address),
            wordCopyRemove state destination)
      | .store | .store8 | .store16 | .store32 =>
          (.mem operator (wordCopyLookup state destination)
            (wordCopyLookup state address), state)

def wordCopyMerge (left right : WordCopyState) : WordCopyState :=
  { aliases := left.aliases.filter (fun entry =>
      lookupNatInfo entry.1 right.aliases == some entry.2),
    storeToEq := left.storeToEq.filter (fun entry =>
      lookupNatInfo entry.1 right.storeToEq == some entry.2) }

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

def wordCopyProg [WordCseHash α] :
    WordCopyState → WordProg α → WordProg α × WordCopyState
  | state, .skip => (.skip, state)
  | state, .move priority moves =>
      let destinations := moves.map Prod.fst
      let sources := moves.map Prod.snd
      if destinations.any (fun name => name ∈ sources) then
        (.move priority moves, wordCopyEmpty)
      else
        let (moves, state) := wordCopyMoves state moves
        (.move priority moves, state)
  | state, .assign destination (.var source) =>
      let source := wordCopyLookup state source
      (.assign destination (.var source),
        wordCopySet (wordCopyRemove state destination) destination source)
  | state, .assign destination value =>
      (.assign destination (wordCopyExp state value), wordCopyRemove state destination)
  | state, .inst instruction =>
      let (instruction, state) := wordCopyInst state instruction
      (.inst instruction, state)
  | state, .get destination store =>
      /- `copy_prop_prog (Get n name)` (`word_copyScript.sml:338-346`): a
         known stored value becomes a copy or the instruction disappears, and
         otherwise the read records itself as the store's current value. -/
      match wordCopyLookupStoreEq state (wordCseStoreCode store) with
      | none =>
          (.get destination store,
            wordCopySetStoreEq (wordCopyRemove state destination)
              (wordCseStoreCode store) destination)
      | some value =>
          if value == destination then (.skip, state)
          else
            let (moves, state) := wordCopyMoves state [(destination, value)]
            (.move 0 moves, state)
  | state, .store address value =>
      (.store (wordCopyExp state address) (wordCopyLookup state value), state)
  | state, .set store value =>
      /- `copy_prop_prog (Set name exp)` (`word_copyScript.sml:332-337`). -/
      match value with
      | .var name =>
          (.set store (.var (wordCopyLookup state name)),
            wordCopySetStoreEq state (wordCseStoreCode store) name)
      | _ => (.set store (wordCopyExp state value), wordCopyEmpty)
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

def wordCopyProp [WordCseHash α] (program : WordProg α) : WordProg α :=
  (wordCopyProg wordCopyEmpty program).1

end Flapjack.RiscV
