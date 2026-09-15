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

end Flapjack.NumSet
