import Std.Data.TreeMap
import Std.Data.TreeSet
import Flapjack.NatDedup
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

/-! Cake's `num_map` is a Patricia tree.  `insert` changes a value without
    making that key the head of the observable `toAList`; the observable order
    is the canonical Patricia traversal for the current key set. -/
def wordHeuristicCanonicalize (counts : NatInfoMap WordHeuristicCounts) :
    NatInfoMap WordHeuristicCounts :=
  (NumSet.fromList (counts.map Prod.fst)).filterMap (fun name =>
    match lookupNatInfo name counts with
    | some value => some (name, value)
    | none => none)

def wordHeuristicUpdate (name : Nat)
    (update : WordHeuristicCounts → WordHeuristicCounts)
    (counts : NatInfoMap WordHeuristicCounts) :
    NatInfoMap WordHeuristicCounts :=
  let value := match lookupNatInfo name counts with
    | some value => value
    | none => wordHeuristicZero
  wordHeuristicCanonicalize
    ((name, update value) :: counts.filter (fun entry => entry.1 != name))

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
      wordHeuristicAddLhsReg name (wordHeuristicAddLhsRegs names counts)

def wordHeuristicAddRhsRegs : List Nat → NatInfoMap WordHeuristicCounts →
    NatInfoMap WordHeuristicCounts
  | [], counts => counts
  | name :: names, counts =>
      wordHeuristicAddRhsReg name (wordHeuristicAddRhsRegs names counts)

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
  | .memOffset operator destination _ _, counts =>
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
  (NumSet.fromList (wordHeuristicKeys left ++ wordHeuristicKeys right)).filterMap
    (fun name =>
      let leftValue := match lookupNatInfo name left with
        | some value => value
        | none => wordHeuristicZero
      let rightValue := match lookupNatInfo name right with
        | some value => value
        | none => wordHeuristicZero
      some (name, wordHeuristicMax leftValue rightValue))

def wordHeuristicMergeCalls (left right : List Nat) : List Nat :=
  NumSet.fromList (left ++ right)

def wordHeuristicAddCall (counts : NatInfoMap WordHeuristicCounts)
    (calls : List Nat) : List Nat :=
  wordHeuristicMergeCalls calls (wordHeuristicKeys counts)

def wordHeuristicMoves (moves : List (Nat × Nat))
    (counts : NatInfoMap WordHeuristicCounts) : NatInfoMap WordHeuristicCounts :=
  /- Cake's `get_heu` uses `FOLDR add1_lhs_reg` over all move sources,
     after `FOLDR add1_rhs_reg` over all move destinations.  Updating a
     complete move pair at once changes the source tree's values; the
     resulting association-list order is the Patricia traversal. -/
  wordHeuristicAddLhsRegs (moves.map Prod.fst)
    (wordHeuristicAddRhsRegs (moves.map Prod.snd) counts)

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

`wordHeuristicUpdate` above rebuilds the Patricia traversal after each update,
so every counter bump costs a full traversal and a full copy;
`wordHeuristicMaxAll` also reconstructs the source key set at every `ite` and
every handled call.
On a function with `k` call sites the traversal alone measures cubic, and it
dominates the whole Word back end: at `k = 200` it is 94% of
`cakeWordStackVarCount`, which is itself half of the per-function cost.

The state below carries the same information in a `Std.TreeMap`, together
with a monotonically increasing stamp for updates.  `toNatInfoMap` rebuilds
the source Patricia traversal from the current key set, so the order remains
observable through `wordHeuristicKeys`.  Lookup and update become
logarithmic, so a traversal is `O(n log n)` rather than cubic.
`Flapjack/Test/HeuristicsFastParity.lean` checks that correspondence against
the reference definitions, list order included. -/

structure WordHeuristicCountMap where
  /-- Key to its counters.  No insertion order is retained: the observable
      order is reconstructed from the key set by `toNatInfoMap`, exactly as
      Cake's `toAList` traversal reconstructs it from a Patricia tree. -/
  entries : Std.TreeMap Nat WordHeuristicCounts := ∅

namespace WordHeuristicCountMap

def lookup (counts : WordHeuristicCountMap) (name : Nat) :
    Option WordHeuristicCounts :=
  counts.entries[name]?

/-- `wordHeuristicUpdate`: bump one counter in the source map. -/
def update (name : Nat) (update : WordHeuristicCounts → WordHeuristicCounts)
    (counts : WordHeuristicCountMap) : WordHeuristicCountMap :=
  { entries := counts.entries.alter name (fun previous =>
      some (update (previous.getD wordHeuristicZero))) }

/-- The association list the reference definition would have built: entries in
    canonical Patricia traversal order for the current key set.  A `TreeMap`'s
    `keys` are already distinct and ascending, so the quadratic membership
    scan in `NumSet.fromList` has nothing to remove. -/
def toNatInfoMap (counts : WordHeuristicCountMap) :
    NatInfoMap WordHeuristicCounts :=
  (NumSet.fromDistinctList counts.entries.keys).filterMap (fun name =>
    match counts.entries[name]? with
    | some value => some (name, value)
    | none => none)

def keys (counts : WordHeuristicCountMap) : List Nat :=
  NumSet.fromDistinctList counts.entries.keys

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

/-- `wordHeuristicMaxAll`.  The source result is a Patricia-tree union, so its
    observable key order is reconstructed by `toNatInfoMap`. -/
def WordHeuristicCountMap.maxAll (left right : WordHeuristicCountMap) :
    WordHeuristicCountMap :=
  /- `wordHeuristicMax` is componentwise `max` and `wordHeuristicZero` is all
     zeros, so a key present on only one side keeps its own value: the
     reference's `max value wordHeuristicZero` is the identity.  That makes
     the union a direct tree merge, rather than materializing both key lists
     and rebuilding the map one `update` at a time. -/
  { entries := Std.TreeMap.mergeWith (fun _ leftValue rightValue =>
      wordHeuristicMax leftValue rightValue) left.entries right.entries }

/-- The self-call list, carried with a set mirror of its own membership so
    that `wordHeuristicMergeCalls`'s `name ∈ calls` test is not linear.  The
    list itself is maintained in exactly the reference order. -/
structure WordHeuristicCallSet where
  names : List Nat := []
  seen : Std.TreeSet Nat := ∅

/-- `wordHeuristicMergeCalls`. -/
def WordHeuristicCallSet.merge (left : WordHeuristicCallSet) (right : List Nat) :
    WordHeuristicCallSet :=
  let seen := right.foldl
    (fun calls name =>
      if calls.seen.contains name then calls
      else { names := name :: calls.names, seen := calls.seen.insert name })
    left
  { names := NumSet.fromList (left.names ++ right), seen := seen.seen }

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
  | .memOffset operator destination _ _, counts =>
      match operator with
      | .load | .load8 | .load16 | .load32 => counts.addLhsMem destination
      | .store | .store8 | .store16 | .store32 => counts.addRhsMem destination

def wordHeuristicAddLhsRegsFast : List Nat → WordHeuristicCountMap →
    WordHeuristicCountMap
  | [], counts => counts
  | name :: names, counts =>
      (wordHeuristicAddLhsRegsFast names counts).addLhsReg name

def wordHeuristicAddRhsRegsFast : List Nat → WordHeuristicCountMap →
    WordHeuristicCountMap
  | [], counts => counts
  | name :: names, counts =>
      (wordHeuristicAddRhsRegsFast names counts).addRhsReg name

def wordHeuristicMovesFast : List (Nat × Nat) → WordHeuristicCountMap →
    WordHeuristicCountMap
  | moves, counts =>
      wordHeuristicAddLhsRegsFast (moves.map Prod.fst)
        (wordHeuristicAddRhsRegsFast (moves.map Prod.snd) counts)

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
