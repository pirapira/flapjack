/-!
Executable list-backed model of the `num_set` operations used by Pancake.

The list is only the input representation.  `fromList` reconstructs the
Patricia-tree insertion and `toAList` traversal used by CakeML's `sptree`, so
the observable order is preserved at compiler boundaries.
-/

namespace Flapjack.NumSet

def insertList (name : Nat) (names : List Nat) : List Nat :=
  if name ∈ names then names else name :: names

def toSet : List Nat → List Nat
  | [] => []
  | name :: names => insertList name (toSet names)

inductive Tree where
  | empty
  | singleton
  | branch (left right : Tree)
  | branchSingleton (left right : Tree)

def lrnextFuel : Nat → Nat → Nat
  | 0, _ => 1
  | _fuel + 1, 0 => 1
  | fuel + 1, value + 1 =>
      2 * lrnextFuel fuel (value / 2)

def lrnext (value : Nat) : Nat :=
  lrnextFuel (value + 1) value

def insertFuel : Nat → Nat → Tree → Tree
  | 0, _, tree => tree
  | _fuel + 1, 0, .empty => .singleton
  | _fuel + 1, 0, .singleton => .singleton
  | _fuel + 1, 0, .branch left right => .branchSingleton left right
  | _fuel + 1, 0, .branchSingleton left right => .branchSingleton left right
  | fuel + 1, key + 1, .empty =>
      if (key + 1) % 2 = 0 then
        .branch (insertFuel fuel (((key + 1) - 1) / 2) .empty) .empty
      else
        .branch .empty (insertFuel fuel (((key + 1) - 1) / 2) .empty)
  | fuel + 1, key + 1, .singleton =>
      if (key + 1) % 2 = 0 then
        .branchSingleton (insertFuel fuel (((key + 1) - 1) / 2) .empty) .empty
      else
        .branchSingleton .empty (insertFuel fuel (((key + 1) - 1) / 2) .empty)
  | fuel + 1, key + 1, .branch left right =>
      if (key + 1) % 2 = 0 then
        .branch (insertFuel fuel (((key + 1) - 1) / 2) left) right
      else
        .branch left (insertFuel fuel (((key + 1) - 1) / 2) right)
  | fuel + 1, key + 1, .branchSingleton left right =>
      if (key + 1) % 2 = 0 then
        .branchSingleton (insertFuel fuel (((key + 1) - 1) / 2) left) right
      else
        .branchSingleton left (insertFuel fuel (((key + 1) - 1) / 2) right)

def insert (key : Nat) (tree : Tree) : Tree :=
  insertFuel (key + 1) key tree

def toAList : Tree → Nat → List Nat → List Nat
  | .empty, _, accumulated => accumulated
  | .singleton, index, accumulated => index :: accumulated
  | .branch left right, index, accumulated =>
      let increment := lrnext index
      toAList right (index + increment)
        (toAList left (index + 2 * increment) accumulated)
  | .branchSingleton left right, index, accumulated =>
      let increment := lrnext index
      toAList right (index + increment)
        (index :: toAList left (index + 2 * increment) accumulated)

def fromList (set : List Nat) : List Nat :=
  let tree := (toSet set).foldr (fun key tree => insert key tree) .empty
  toAList tree 0 []

/-! Reconstruct a Patricia tree from the key order returned by `toAList`.
    Cake's `fromAList` folds these already-materialized keys from the left;
    this is distinct from `fromList`, whose input is a source list and is
    folded from the right by `list_to_num_set`.  Keeping the two operations
    separate matters because the mixed traversal order is observable in
    allocator node numbering. -/
def fromAList (set : List Nat) : List Nat :=
  let tree := set.foldl (fun tree key => insert key tree) .empty
  toAList tree 0 []

/-- `fromList` for a list whose entries are already known to be distinct.
    `toSet` is the identity on such a list -- it only removes duplicates, at
    the cost of a membership scan per element -- so the Patricia
    reconstruction can run on the input directly.  `NumSet.fromDistinctList_eq`
    pins the two together. -/
def fromDistinctList (set : List Nat) : List Nat :=
  toAList (set.foldr (fun key tree => insert key tree) .empty) 0 []

theorem toSet_eq_self_of_nodup : ∀ {names : List Nat}, names.Nodup →
    toSet names = names
  | [], _ => rfl
  | name :: names, nodup => by
      have tail : toSet names = names := toSet_eq_self_of_nodup nodup.of_cons
      have notMem : name ∉ names := by
        simpa using (List.nodup_cons.mp nodup).1
      simp [toSet, insertList, tail, notMem]

theorem fromDistinctList_eq {names : List Nat} (nodup : names.Nodup) :
    fromDistinctList names = fromList names := by
  simp [fromDistinctList, fromList, toSet_eq_self_of_nodup nodup]

end Flapjack.NumSet
