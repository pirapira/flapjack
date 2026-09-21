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
     representation stores the visible representative directly. -/
  storeToEq : NatInfoMap Nat
  /- Cake's class identity is retained separately so branch merges do not
     confuse independently-created classes with the same representative. -/
  classOf : NatInfoMap Nat
  classRep : NatInfoMap Nat
  classStore : NatInfoMap Nat
  classNext : Nat
  /- Production states cache the same first-binding maps in trees.  The
     association lists remain the proof-facing Cake representation; literals
     in focused tests use the default `indicesReady = false`. -/
  indicesReady : Bool := false
  aliasIndex : Std.TreeMap Nat Nat := ∅
  classOfIndex : Std.TreeMap Nat Nat := ∅
  classRepIndex : Std.TreeMap Nat Nat := ∅
  /- Lookup-only indexes for Cake's store equivalence maps.  The association
     lists remain authoritative for branch intersection and preserve Cake's
     order; these indexes only avoid repeated linear lookups on Get. -/
  storeToEqIndex : Std.TreeMap Nat Nat := ∅
  classStoreIndex : Std.TreeMap Nat Nat := ∅
  deriving Repr

def wordCopyEmpty : WordCopyState :=
  { aliases := [], storeToEq := [], classOf := [], classRep := [],
    classStore := [], classNext := 0, indicesReady := true,
    storeToEqIndex := ∅, classStoreIndex := ∅ }

def wordCopyLookupIndexed (ready : Bool) (index : Std.TreeMap Nat Nat)
    (entries : NatInfoMap Nat) (name : Nat) : Option Nat :=
  if ready then index[name]? else lookupNatInfo name entries

def wordCopyLookup (state : WordCopyState) (name : Nat) : Nat :=
  /- Cake's `lookup_eq` resolves the class indirection first: `to_eq` maps
     the name to an equivalence class and `from_eq` stores that class's
     current representative.  The flattened alias table is still useful for
     names outside a live class, but it must not shadow a representative
     update.  Without this order, a later `set_eq` changed `classRep` while
     old members continued to read their stale alias (the fp_pow4 chain
     329 <- 305, 345 <- 329, 413 <- 329). -/
  match wordCopyLookupIndexed state.indicesReady state.classOfIndex
      state.classOf name with
  | some classId =>
      (wordCopyLookupIndexed state.indicesReady state.classRepIndex
        state.classRep classId).getD name
  | none =>
      (wordCopyLookupIndexed state.indicesReady state.aliasIndex
        state.aliases name).getD name

def wordCopyUpdate (aliases : NatInfoMap Nat) (name value : Nat) : NatInfoMap Nat :=
  (name, value) :: aliases.filter (fun entry => entry.1 != name)

def wordCopyIsAlloc (name : Nat) : Bool := name % 4 == 1

def wordCopyIndex (entries : NatInfoMap Nat) : Std.TreeMap Nat Nat :=
  entries.foldr (fun entry index => index.insert entry.1 entry.2) ∅

def wordCopyRemove (state : WordCopyState) (name : Nat) : WordCopyState :=
  if (wordCopyLookupIndexed state.indicesReady state.classOfIndex
      state.classOf name).isSome then wordCopyEmpty else state

/-! `set_eq` (`word_copyScript.sml:204-225`).  Cake's equivalence class is
    represented by the *destination* of the copy. -/
def wordCopySet (state : WordCopyState) (destination source : Nat) : WordCopyState :=
  if wordCopyIsAlloc destination && wordCopyIsAlloc source then
    let others := state.aliases.filter (fun entry =>
      entry.1 != destination && entry.1 != source)
    let aliasIndex := if state.indicesReady then
        ((state.aliasIndex.erase destination).erase source)
          |>.insert destination destination
      else ∅
    let aliasIndex := if state.indicesReady then
        aliasIndex.insert source destination
      else ∅
    match wordCopyLookupIndexed state.indicesReady state.classOfIndex
        state.classOf source with
    | some classId =>
        if (wordCopyLookupIndexed state.indicesReady state.classRepIndex
            state.classRep classId).isSome then
          { state with
            aliases := (destination, destination) ::
              (source, destination) :: others
            classOf := wordCopyUpdate state.classOf destination classId
            classRep := wordCopyUpdate state.classRep classId destination
            aliasIndex := aliasIndex
            classOfIndex := if state.indicesReady then
                state.classOfIndex.insert destination classId
              else ∅
            classRepIndex := if state.indicesReady then
                state.classRepIndex.insert classId destination
              else ∅ }
        else
          { state with
            aliases := (destination, destination) ::
              (source, destination) :: others
            classOf := (destination, state.classNext) ::
              (source, state.classNext) :: state.classOf
            classRep := (state.classNext, destination) :: state.classRep
            classNext := state.classNext + 1
            aliasIndex := aliasIndex
            classOfIndex := if state.indicesReady then
                (state.classOfIndex.insert destination state.classNext).insert
                  source state.classNext
              else ∅
            classRepIndex := if state.indicesReady then
                state.classRepIndex.insert state.classNext destination
              else ∅ }
    | none =>
        { state with
          aliases := (destination, destination) ::
            (source, destination) :: others
          classOf := (destination, state.classNext) ::
              (source, state.classNext) :: state.classOf
          classRep := (state.classNext, destination) :: state.classRep
          classNext := state.classNext + 1
          aliasIndex := aliasIndex
          classOfIndex := if state.indicesReady then
              (state.classOfIndex.insert destination state.classNext).insert
                source state.classNext
            else ∅
          classRepIndex := if state.indicesReady then
              state.classRepIndex.insert state.classNext destination
            else ∅ }
  else state

/- `lookup_store_eq` (`word_copyScript.sml:252-260`).  Cake resolves the
    recorded internal class through `from_eq` and reports nothing when that
    class no longer exists; the port's representative is live exactly when the
    alias map still carries it. -/
def wordCopyLookupStoreEq (state : WordCopyState) (store : Nat) : Option Nat :=
  match (if state.indicesReady then state.storeToEqIndex[store]?
    else lookupNatInfo store state.storeToEq) with
  | none => none
  | some representative =>
      if (wordCopyLookupIndexed state.indicesReady state.aliasIndex
          state.aliases representative).isSome then
        some representative
      else none

/-! `set_store_eq` (`word_copyScript.sml:233-250`).  The SSA invariant makes
    the source an allocatable name, so a name without a class gets its own
    singleton class and a name with one reuses it. -/
def wordCopySetStoreEq (state : WordCopyState) (store name : Nat) : WordCopyState :=
  if wordCopyIsAlloc name then
    match wordCopyLookupIndexed state.indicesReady state.classOfIndex
        state.classOf name with
    | some classId =>
        if (wordCopyLookupIndexed state.indicesReady state.classRepIndex
            state.classRep classId).isSome then
          { state with
            storeToEq := (store, wordCopyLookup state name) ::
              state.storeToEq.filter (fun entry => entry.1 != store),
            storeToEqIndex := if state.indicesReady then
                (state.storeToEqIndex.erase store).insert store
                  (wordCopyLookup state name)
              else ∅,
            classStore := (store, classId) ::
              state.classStore.filter (fun entry => entry.1 != store),
            classStoreIndex := if state.indicesReady then
                (state.classStoreIndex.erase store).insert store classId
              else ∅ }
        else
          { state with
            aliases := (name, name) ::
              state.aliases.filter (fun entry => entry.1 != name)
            storeToEq := (store, name) ::
              state.storeToEq.filter (fun entry => entry.1 != store),
            storeToEqIndex := if state.indicesReady then
                (state.storeToEqIndex.erase store).insert store name
              else ∅,
            classOf := (name, state.classNext) :: state.classOf,
            classRep := (state.classNext, name) :: state.classRep,
            classStore := (store, state.classNext) ::
              state.classStore.filter (fun entry => entry.1 != store),
            classStoreIndex := if state.indicesReady then
                (state.classStoreIndex.erase store).insert store state.classNext
              else ∅,
            classNext := state.classNext + 1,
            aliasIndex := if state.indicesReady then
                (state.aliasIndex.erase name).insert name name
              else ∅,
            classOfIndex := if state.indicesReady then
                state.classOfIndex.insert name state.classNext
              else ∅,
            classRepIndex := if state.indicesReady then
                state.classRepIndex.insert state.classNext name
              else ∅ }
    | none =>
        { state with
          aliases := (name, name) ::
            state.aliases.filter (fun entry => entry.1 != name)
          storeToEq := (store, name) ::
            state.storeToEq.filter (fun entry => entry.1 != store),
          storeToEqIndex := if state.indicesReady then
              (state.storeToEqIndex.erase store).insert store name
            else ∅,
          classOf := (name, state.classNext) :: state.classOf,
          classRep := (state.classNext, name) :: state.classRep,
          classStore := (store, state.classNext) ::
            state.classStore.filter (fun entry => entry.1 != store),
          classStoreIndex := if state.indicesReady then
              (state.classStoreIndex.erase store).insert store state.classNext
            else ∅,
          classNext := state.classNext + 1,
          aliasIndex := if state.indicesReady then
              (state.aliasIndex.erase name).insert name name
            else ∅,
          classOfIndex := if state.indicesReady then
              state.classOfIndex.insert name state.classNext
            else ∅,
          classRepIndex := if state.indicesReady then
              state.classRepIndex.insert state.classNext name
            else ∅ }
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
  | .memOffset operator destination address offset =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          (.memOffset operator destination (wordCopyLookup state address) offset,
            wordCopyRemove state destination)
      | .store | .store8 | .store16 | .store32 =>
          (.memOffset operator (wordCopyLookup state destination)
            (wordCopyLookup state address) offset, state)

def wordCopyMerge (left right : WordCopyState) : WordCopyState :=
  let rightAliases := if right.indicesReady then right.aliasIndex
    else wordCopyIndex right.aliases
  let rightClassOf := if right.indicesReady then right.classOfIndex
    else wordCopyIndex right.classOf
  let rightClassRep := if right.indicesReady then right.classRepIndex
    else wordCopyIndex right.classRep
  let rightStoreToEq := if right.indicesReady then right.storeToEqIndex
    else wordCopyIndex right.storeToEq
  let rightClassStore := if right.indicesReady then right.classStoreIndex
    else wordCopyIndex right.classStore
  let aliases := left.aliases.filter (fun entry =>
      rightAliases[entry.1]? == some entry.2 &&
      match wordCopyLookupIndexed left.indicesReady left.classOfIndex
          left.classOf entry.1, rightClassOf[entry.1]? with
      | some leftClass, some rightClass =>
          leftClass == rightClass &&
            wordCopyLookupIndexed left.indicesReady left.classRepIndex
              left.classRep leftClass == some entry.2 &&
            rightClassRep[leftClass]? == some entry.2
      | _, _ => false)
  let classOf := left.classOf.filter (fun entry =>
      rightClassOf[entry.1]? == some entry.2)
  let classRep := left.classRep.filter (fun entry =>
      rightClassRep[entry.1]? == some entry.2)
  let storeToEq := left.storeToEq.filter (fun entry =>
      rightStoreToEq[entry.1]? == some entry.2)
  let classStore := left.classStore.filter (fun entry =>
      rightClassStore[entry.1]? == some entry.2)
  let ready := left.indicesReady && right.indicesReady
  { aliases := aliases,
    storeToEq := storeToEq,
    classOf := classOf,
    classRep := classRep,
    classStore := classStore,
    classNext := max left.classNext right.classNext,
    indicesReady := ready,
    aliasIndex := if ready then wordCopyIndex aliases else ∅,
    classOfIndex := if ready then wordCopyIndex classOf else ∅,
    classRepIndex := if ready then wordCopyIndex classRep else ∅,
    storeToEqIndex := if ready then wordCopyIndex storeToEq else ∅,
    classStoreIndex := if ready then wordCopyIndex classStore else ∅ }

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
  | state, .opCurrHeap operator destination source =>
      let source' := wordCopyLookup state source
      let source'' := if source' == destination then source else source'
      (.opCurrHeap operator destination source'', wordCopyRemove state destination)
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
  | _state, .loop liveIn body liveOut =>
      let (body, _) := wordCopyProg wordCopyEmpty body
      (.loop liveIn body liveOut, wordCopyEmpty)
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
            (wordCopyShareExp state address), wordCopyRemove state name)
  | state, .break label => (.break label, state)
  | state, .continue label => (.continue label, state)
  | _state, program => (program, wordCopyEmpty)
termination_by _ program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordCopyProp [WordCseHash α] (program : WordProg α) : WordProg α :=
  (wordCopyProg wordCopyEmpty program).1

end Flapjack.RiscV
