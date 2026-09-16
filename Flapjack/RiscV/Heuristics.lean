import Std.Data.TreeMap
import Std.Data.TreeSet
import Flapjack.RiscV.RegAlloc

/-!
# CakeML Word allocation heuristics

CakeML computes a small usage summary immediately before register allocation.
The five counters record whether a variable occurs on the left-hand side of a
constant, register, or memory operation, and on the right-hand side of a
register or memory operation.  This module ports that executable summary for
the Word fragment represented by Flapjack.

The source allocator also attaches priorities to move preferences.  The
existing graph allocator accepts unprioritized pairs for compatibility, while
the entry points below retain the source priorities and pass them to the
same coalescing machinery.
-/

namespace Flapjack

structure WordHeuristicCounts where
  lhsConst : Nat
  lhsReg : Nat
  lhsMem : Nat
  rhsReg : Nat
  rhsMem : Nat
  deriving DecidableEq, Repr

def wordHeuristicZero : WordHeuristicCounts :=
  { lhsConst := 0, lhsReg := 0, lhsMem := 0, rhsReg := 0, rhsMem := 0 }

def wordHeuristicUpdate (name : Nat)
    (update : WordHeuristicCounts → WordHeuristicCounts)
    (counts : NatInfoMap WordHeuristicCounts) :
    NatInfoMap WordHeuristicCounts :=
  let value := match lookupNatInfo name counts with
    | some value => value
    | none => wordHeuristicZero
  (name, update value) :: counts.filter (fun entry => entry.1 != name)

def wordHeuristicAddLhsConst (name : Nat)
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  wordHeuristicUpdate name (fun value => { value with lhsConst := value.lhsConst + 1 }) counts

def wordHeuristicAddLhsReg (name : Nat)
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  wordHeuristicUpdate name (fun value => { value with lhsReg := value.lhsReg + 1 }) counts

def wordHeuristicAddLhsMem (name : Nat)
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  wordHeuristicUpdate name (fun value => { value with lhsMem := value.lhsMem + 1 }) counts

def wordHeuristicAddRhsReg (name : Nat)
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  wordHeuristicUpdate name (fun value => { value with rhsReg := value.rhsReg + 1 }) counts

def wordHeuristicAddRhsMem (name : Nat)
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  wordHeuristicUpdate name (fun value => { value with rhsMem := value.rhsMem + 1 }) counts

def wordHeuristicAddLhsRegs : List Nat → NatInfoMap WordHeuristicCounts →
    NatInfoMap WordHeuristicCounts
  | [], counts => counts
  | name :: names, counts =>
      wordHeuristicAddLhsRegs names (wordHeuristicAddLhsReg name counts)

def wordHeuristicAddRhsRegs : List Nat → NatInfoMap WordHeuristicCounts →
    NatInfoMap WordHeuristicCounts
  | [], counts => counts
  | name :: names, counts =>
      wordHeuristicAddRhsRegs names (wordHeuristicAddRhsReg name counts)

def wordHeuristicInst {α : Type} : WordInst α → NatInfoMap WordHeuristicCounts →
    NatInfoMap WordHeuristicCounts
  | .arith operation, counts =>
      match operation with
      | .longMul left right sourceLeft sourceRight =>
          wordHeuristicAddLhsReg right
            (wordHeuristicAddLhsReg left
              (wordHeuristicAddRhsReg sourceRight
                (wordHeuristicAddRhsReg sourceLeft counts)))
      | .longDiv left right sourceLeft sourceRight quotient =>
          wordHeuristicAddLhsReg right
            (wordHeuristicAddLhsReg left
              (wordHeuristicAddRhsReg quotient
                (wordHeuristicAddRhsReg sourceRight
                  (wordHeuristicAddRhsReg sourceLeft counts))))
      | .addCarry destination carry sourceLeft sourceRight carryIn =>
          wordHeuristicAddLhsReg carry
            (wordHeuristicAddLhsReg destination
              (wordHeuristicAddRhsReg carryIn
                (wordHeuristicAddRhsReg sourceRight
                  (wordHeuristicAddRhsReg sourceLeft counts))))
      | .cakeAddCarry destination sourceLeft sourceRight carry =>
          wordHeuristicAddLhsReg carry
            (wordHeuristicAddLhsReg destination
              (wordHeuristicAddRhsReg sourceRight
                (wordHeuristicAddRhsReg sourceLeft
                  (wordHeuristicAddRhsReg carry counts))))
      | .div destination dividend divisor =>
          wordHeuristicAddLhsReg destination
            (wordHeuristicAddRhsReg divisor
              (wordHeuristicAddRhsReg dividend counts))
      | .binOp _ destination sourceLeft sourceRight =>
          let addRight :=
            match sourceRight with
            | .reg register => wordHeuristicAddRhsReg register
            | .imm _ => id
          addRight (wordHeuristicAddLhsReg destination
            (wordHeuristicAddRhsReg sourceLeft counts))
      | .shift _ destination sourceLeft sourceRight =>
          let addRight :=
            match sourceRight with
            | .reg register => wordHeuristicAddRhsReg register
            | .imm _ => id
          addRight (wordHeuristicAddLhsReg destination
            (wordHeuristicAddRhsReg sourceLeft counts))
  | .const destination _, counts =>
      wordHeuristicAddLhsConst destination counts
  | .mem operator destination _, counts =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          wordHeuristicAddLhsMem destination counts
      | .store | .store8 | .store16 | .store32 =>
          wordHeuristicAddRhsMem destination counts

def wordHeuristicMax (left right : WordHeuristicCounts) : WordHeuristicCounts :=
  { lhsConst := max left.lhsConst right.lhsConst
    lhsReg := max left.lhsReg right.lhsReg
    lhsMem := max left.lhsMem right.lhsMem
    rhsReg := max left.rhsReg right.rhsReg
    rhsMem := max left.rhsMem right.rhsMem }

def wordHeuristicKeys (counts : NatInfoMap WordHeuristicCounts) : List Nat :=
  counts.map Prod.fst

def wordHeuristicMaxAll (left right : NatInfoMap WordHeuristicCounts) :
    NatInfoMap WordHeuristicCounts :=
  ((wordHeuristicKeys left ++ wordHeuristicKeys right).eraseDups).foldl
    (fun result name =>
      let leftValue := match lookupNatInfo name left with
        | some value => value
        | none => wordHeuristicZero
      let rightValue := match lookupNatInfo name right with
        | some value => value
        | none => wordHeuristicZero
      wordHeuristicUpdate name (fun _ => wordHeuristicMax leftValue rightValue) result)
    []

def wordHeuristicMergeCalls (left right : List Nat) : List Nat :=
  right.foldl (fun calls name => if name ∈ calls then calls else name :: calls) left

def wordHeuristicAddCall (counts : NatInfoMap WordHeuristicCounts)
    (calls : List Nat) : List Nat :=
  wordHeuristicMergeCalls calls (wordHeuristicKeys counts)

def wordHeuristicMoves (moves : List (Nat × Nat))
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  match moves with
  | [] => counts
  | (left, right) :: moves =>
      wordHeuristicMoves moves
        (wordHeuristicAddLhsReg left (wordHeuristicAddRhsReg right counts))

def wordHeuristic (currentFunction : Nat) : WordProg α →
    NatInfoMap WordHeuristicCounts × List Nat →
    NatInfoMap WordHeuristicCounts × List Nat
  | .move _ moves, (counts, calls) => (wordHeuristicMoves moves counts, calls)
  | .inst instruction, (counts, calls) => (wordHeuristicInst instruction counts, calls)
  | .get destination _, (counts, calls) =>
      (wordHeuristicAddLhsMem destination counts, calls)
  | .set _ (.var source), (counts, calls) =>
      (wordHeuristicAddRhsMem source counts, calls)
  | .opCurrHeap _ destination source, (counts, calls) =>
      (wordHeuristicAddLhsReg destination
        (wordHeuristicAddRhsReg source counts), calls)
  | .locValue destination _, (counts, calls) =>
      (wordHeuristicAddLhsReg destination counts, calls)
  | .seq first second, state =>
      wordHeuristic currentFunction second (wordHeuristic currentFunction first state)
  | .mustTerminate body, state => wordHeuristic currentFunction body state
  | .ite _ condition right thenBranch elseBranch, (counts, calls) =>
      let thenResult := wordHeuristic currentFunction thenBranch (counts, calls)
      let elseResult := wordHeuristic currentFunction elseBranch (counts, calls)
      let merged := wordHeuristicMaxAll thenResult.1 elseResult.1
      let mergedCalls := wordHeuristicMergeCalls thenResult.2 elseResult.2
      let merged := wordHeuristicAddRhsReg condition merged
      match right with
      | .imm _ => (merged, mergedCalls)
      | .reg source =>
          (wordHeuristicAddRhsReg source merged, mergedCalls)
  | .call returns target _ handler, (counts, calls) =>
      let calls := match target with
        | some target => if target = currentFunction then
            wordHeuristicAddCall counts calls else calls
        | none => calls
      match returns with
      | none => (counts, calls)
      | some (_, _, returnCode, _, _) =>
          let returnResult := wordHeuristic currentFunction returnCode (counts, calls)
          match handler with
          | none => (returnResult.1, calls)
          | some (_, handlerCode, _, _) =>
              let handlerResult := wordHeuristic currentFunction handlerCode (counts, calls)
              (wordHeuristicMaxAll returnResult.1 handlerResult.1,
                wordHeuristicMergeCalls returnResult.2 handlerResult.2)
  | .shareInst operator name _, (counts, calls) =>
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          (wordHeuristicAddLhsMem name counts, calls)
      | .store | .store8 | .store16 | .store32 =>
          (wordHeuristicAddRhsMem name counts, calls)
  | .loop _ body _, state => wordHeuristic currentFunction body state
  | _, state => state
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! ## Tree-backed counter state

`wordHeuristicUpdate` above moves the updated key to the front of the
association list and rebuilds the remainder with `List.filter`, so every
counter bump costs a full traversal and a full copy; `wordHeuristicMaxAll`
adds an `eraseDups` on top of that at every `ite` and every handled call.
On a function with `k` call sites the traversal alone measures cubic, and it
dominates the whole Word back end: at `k = 200` it is 94% of
`cakeWordStackVarCount`, which is itself half of the per-function cost.

The state below carries the same information in a `Std.TreeMap`, together
with a monotonically increasing stamp recording when each key was last
updated.  Because `wordHeuristicUpdate` always moves the updated key to the
front, the association list it maintains is exactly the entries in order of
decreasing stamp, so `toNatInfoMap` reproduces the list-based result
verbatim -- including its order, which the reference definition makes
observable through `wordHeuristicKeys`.  Lookup and update become
logarithmic, so a traversal is `O(n log n)` rather than cubic.
`Flapjack/Test/HeuristicsFastParity.lean` checks that correspondence against
the reference definitions, list order included. -/

structure WordHeuristicCountMap where
  /-- Key to its update stamp and counters. -/
  entries : Std.TreeMap Nat (Nat × WordHeuristicCounts) := ∅
  /-- Update stamp back to its key, so the association list can be recovered
      in stamp order without sorting. -/
  order : Std.TreeMap Nat Nat := ∅
  next : Nat := 0

namespace WordHeuristicCountMap

def lookup (counts : WordHeuristicCountMap) (name : Nat) :
    Option WordHeuristicCounts :=
  (counts.entries[name]?).map Prod.snd

/-- `wordHeuristicUpdate`: bump one counter and move the key to the front. -/
def update (name : Nat) (update : WordHeuristicCounts → WordHeuristicCounts)
    (counts : WordHeuristicCountMap) : WordHeuristicCountMap :=
  let previous := counts.entries[name]?
  let value := (previous.map Prod.snd).getD wordHeuristicZero
  let order := match previous with
    | some (stamp, _) => counts.order.erase stamp
    | none => counts.order
  { entries := counts.entries.insert name (counts.next, update value)
    order := order.insert counts.next name
    next := counts.next + 1 }

/-- The association list the reference definition would have built: entries
    in order of decreasing update stamp, most recently updated first.
    `order` is keyed by stamp, so folding it left to right visits ascending
    stamps and prepending reverses them into the required order. -/
def toNatInfoMap (counts : WordHeuristicCountMap) :
    NatInfoMap WordHeuristicCounts :=
  counts.order.foldl
    (fun result _ name =>
      match counts.entries[name]? with
      | some (_, value) => (name, value) :: result
      | none => result)
    []

def keys (counts : WordHeuristicCountMap) : List Nat :=
  counts.order.foldl (fun result _ name => name :: result) []

def addLhsConst (name : Nat) (counts : WordHeuristicCountMap) :
    WordHeuristicCountMap :=
  counts.update name (fun value => { value with lhsConst := value.lhsConst + 1 })

def addLhsReg (name : Nat) (counts : WordHeuristicCountMap) :
    WordHeuristicCountMap :=
  counts.update name (fun value => { value with lhsReg := value.lhsReg + 1 })

def addLhsMem (name : Nat) (counts : WordHeuristicCountMap) :
    WordHeuristicCountMap :=
  counts.update name (fun value => { value with lhsMem := value.lhsMem + 1 })

def addRhsReg (name : Nat) (counts : WordHeuristicCountMap) :
    WordHeuristicCountMap :=
  counts.update name (fun value => { value with rhsReg := value.rhsReg + 1 })

def addRhsMem (name : Nat) (counts : WordHeuristicCountMap) :
    WordHeuristicCountMap :=
  counts.update name (fun value => { value with rhsMem := value.rhsMem + 1 })

end WordHeuristicCountMap

/-- `List.eraseDups` with logarithmic membership; keeps the first occurrence
    of every key in its original position, as `List.eraseDups` does. -/
def wordHeuristicEraseDupsAux (seen : Std.TreeSet Nat) :
    List Nat → List Nat
  | [] => []
  | name :: names =>
      if seen.contains name then wordHeuristicEraseDupsAux seen names
      else name :: wordHeuristicEraseDupsAux (seen.insert name) names

def wordHeuristicEraseDups (names : List Nat) : List Nat :=
  wordHeuristicEraseDupsAux ∅ names

/-- `wordHeuristicMaxAll`.  The reference folds `wordHeuristicUpdate` over the
    deduplicated key list starting from the empty map, and every update
    prepends, so the result is that key list reversed.  Inserting in the same
    order here gives ascending stamps, and `toNatInfoMap` reverses them. -/
def WordHeuristicCountMap.maxAll (left right : WordHeuristicCountMap) :
    WordHeuristicCountMap :=
  (wordHeuristicEraseDups (left.keys ++ right.keys)).foldl
    (fun result name =>
      let leftValue := (left.lookup name).getD wordHeuristicZero
      let rightValue := (right.lookup name).getD wordHeuristicZero
      result.update name (fun _ => wordHeuristicMax leftValue rightValue))
    {}

/-- The self-call list, carried with a set mirror of its own membership so
    that `wordHeuristicMergeCalls`'s `name ∈ calls` test is not linear.  The
    list itself is maintained in exactly the reference order. -/
structure WordHeuristicCallSet where
  names : List Nat := []
  seen : Std.TreeSet Nat := ∅

/-- `wordHeuristicMergeCalls`. -/
def WordHeuristicCallSet.merge (left : WordHeuristicCallSet) (right : List Nat) :
    WordHeuristicCallSet :=
  right.foldl
    (fun calls name =>
      if calls.seen.contains name then calls
      else { names := name :: calls.names, seen := calls.seen.insert name })
    left

/-- `wordHeuristicAddCall`. -/
def WordHeuristicCallSet.addCall (calls : WordHeuristicCallSet)
    (counts : WordHeuristicCountMap) : WordHeuristicCallSet :=
  calls.merge counts.keys

def wordHeuristicInstFast {α : Type} : WordInst α → WordHeuristicCountMap →
    WordHeuristicCountMap
  | .arith operation, counts =>
      match operation with
      | .longMul left right sourceLeft sourceRight =>
          (((counts.addRhsReg sourceLeft).addRhsReg sourceRight).addLhsReg
            left).addLhsReg right
      | .longDiv left right sourceLeft sourceRight quotient =>
          ((((counts.addRhsReg sourceLeft).addRhsReg sourceRight).addRhsReg
            quotient).addLhsReg left).addLhsReg right
      | .addCarry destination carry sourceLeft sourceRight carryIn =>
          ((((counts.addRhsReg sourceLeft).addRhsReg sourceRight).addRhsReg
            carryIn).addLhsReg destination).addLhsReg carry
      | .cakeAddCarry destination sourceLeft sourceRight carry =>
          ((((counts.addRhsReg carry).addRhsReg sourceLeft).addRhsReg
            sourceRight).addLhsReg destination).addLhsReg carry
      | .div destination dividend divisor =>
          ((counts.addRhsReg dividend).addRhsReg divisor).addLhsReg destination
      | .binOp _ destination sourceLeft sourceRight =>
          let base := (counts.addRhsReg sourceLeft).addLhsReg destination
          match sourceRight with
          | .reg register => base.addRhsReg register
          | .imm _ => base
      | .shift _ destination sourceLeft sourceRight =>
          let base := (counts.addRhsReg sourceLeft).addLhsReg destination
          match sourceRight with
          | .reg register => base.addRhsReg register
          | .imm _ => base
  | .const destination _, counts => counts.addLhsConst destination
  | .mem operator destination _, counts =>
      match operator with
      | .load | .load8 | .load16 | .load32 => counts.addLhsMem destination
      | .store | .store8 | .store16 | .store32 => counts.addRhsMem destination

def wordHeuristicMovesFast : List (Nat × Nat) → WordHeuristicCountMap →
    WordHeuristicCountMap
  | [], counts => counts
  | (left, right) :: moves, counts =>
      wordHeuristicMovesFast moves ((counts.addRhsReg right).addLhsReg left)

/-- `wordHeuristic` over the hashed state.  Case for case the same traversal;
    only the counter representation differs. -/
def wordHeuristicFast (currentFunction : Nat) : WordProg α →
    WordHeuristicCountMap × WordHeuristicCallSet →
    WordHeuristicCountMap × WordHeuristicCallSet
  | .move _ moves, (counts, calls) => (wordHeuristicMovesFast moves counts, calls)
  | .inst instruction, (counts, calls) => (wordHeuristicInstFast instruction counts, calls)
  | .get destination _, (counts, calls) => (counts.addLhsMem destination, calls)
  | .set _ (.var source), (counts, calls) => (counts.addRhsMem source, calls)
  | .opCurrHeap _ destination source, (counts, calls) =>
      ((counts.addRhsReg source).addLhsReg destination, calls)
  | .locValue destination _, (counts, calls) => (counts.addLhsReg destination, calls)
  | .seq first second, state =>
      wordHeuristicFast currentFunction second (wordHeuristicFast currentFunction first state)
  | .mustTerminate body, state => wordHeuristicFast currentFunction body state
  | .ite _ condition right thenBranch elseBranch, (counts, calls) =>
      let thenResult := wordHeuristicFast currentFunction thenBranch (counts, calls)
      let elseResult := wordHeuristicFast currentFunction elseBranch (counts, calls)
      let merged := WordHeuristicCountMap.maxAll thenResult.1 elseResult.1
      let mergedCalls := thenResult.2.merge elseResult.2.names
      let merged := merged.addRhsReg condition
      match right with
      | .imm _ => (merged, mergedCalls)
      | .reg source => (merged.addRhsReg source, mergedCalls)
  | .call returns target _ handler, (counts, calls) =>
      let calls := match target with
        | some target => if target = currentFunction then calls.addCall counts else calls
        | none => calls
      match returns with
      | none => (counts, calls)
      | some (_, _, returnCode, _, _) =>
          let returnResult := wordHeuristicFast currentFunction returnCode (counts, calls)
          match handler with
          | none => (returnResult.1, calls)
          | some (_, handlerCode, _, _) =>
              let handlerResult := wordHeuristicFast currentFunction handlerCode (counts, calls)
              (WordHeuristicCountMap.maxAll returnResult.1 handlerResult.1,
                returnResult.2.merge handlerResult.2.names)
  | .shareInst operator name _, (counts, calls) =>
      match operator with
      | .load | .load8 | .load16 | .load32 => (counts.addLhsMem name, calls)
      | .store | .store8 | .store16 | .store32 => (counts.addRhsMem name, calls)
  | .loop _ body _, state => wordHeuristicFast currentFunction body state
  | _, state => state
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordProgPrioritizedMoves : WordProg α → List WordMove
  | .move priority moves => moves.map (fun move =>
      { priority := priority, left := move.1, right := move.2 })
  | .assign _ _ | .locValue _ _ => []
  | .seq first second =>
      wordProgPrioritizedMoves first ++ wordProgPrioritizedMoves second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgPrioritizedMoves thenBranch ++ wordProgPrioritizedMoves elseBranch
  | .loop _ body _ | .mustTerminate body => wordProgPrioritizedMoves body
  | .call none _ _ _ => []
  | .call (some (_, _, returnCode, _, _)) _ _ none =>
      wordProgPrioritizedMoves returnCode
  | .call (some (_, _, returnCode, _, _)) _ _ (some (_, body, _, _)) =>
      wordProgPrioritizedMoves body ++ wordProgPrioritizedMoves returnCode
  | _ => []
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordAllocateGraphProgramWithPriorities (program : WordProg α)
    (fixedSources : List Nat) (colours stackStart : Nat) :
    Option (WordGraphAllocation × WordProg α) :=
  let tree := wordClashTree program []
  let forced := wordProgForcedClashes program
  (wordAllocateGraphWithPrioritizedMoves tree forced fixedSources
      (wordProgPrioritizedMoves program) colours stackStart).map
    (fun allocation =>
      (allocation,
        wordApplyColour
          (wordGraphColouringAt allocation.colouring) program))

end Flapjack
