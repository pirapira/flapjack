import Std.Data.TreeSet

/-!
# Deduplicating lists of names

`List.eraseDups` rescans the accumulated prefix for every element, so it is
quadratic.  The compiler uses it on live-variable and key lists whose length
is proportional to the size of the function being compiled, which turns a
single traversal of a function into a cubic cost.

`natEraseDups` is the same function on `List Nat` with the membership test
carried in a `Std.TreeSet`: it keeps the first occurrence of every name in
its original position, so it returns exactly the list `List.eraseDups`
returns, and it is `O(n log n)`.  A `Std.TreeSet` rather than a
`Std.HashSet` so that callers stay reducible by the kernel and their
`decide` regressions keep working.
-/

namespace Flapjack

def natEraseDupsAux (seen : Std.TreeSet Nat) : List Nat → List Nat
  | [] => []
  | name :: names =>
      if seen.contains name then natEraseDupsAux seen names
      else name :: natEraseDupsAux (seen.insert name) names

def natEraseDups (names : List Nat) : List Nat :=
  natEraseDupsAux ∅ names

/-- The elements of a name list as a set, for membership tests that would
    otherwise rescan the list.  Callers keep their lists; only the predicate
    changes, so the values they compute are unchanged. -/
def natSetOfList (names : List Nat) : Std.TreeSet Nat :=
  names.foldl (fun seen name => seen.insert name) ∅

end Flapjack
