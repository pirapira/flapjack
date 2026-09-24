import Flapjack.HolRef

/-!
# Exact `spt`/`num_set` carrier

Counterpart of the HOL `spt` data structure (`HOL/src/finite_maps/sptreeScript.sml`)
and of the CakeML abbreviation `num_set = unit spt`
(`cakeml/misc/miscScript.sml:787`).

HOL's `spt` is defined outside the CakeML submodule, so the datatype itself cannot
carry an `@[hol]` reference into `cakeml/`.  The carrier below mirrors the HOL
constructors exactly:

```
Datatype: spt = LN | LS 'a | BN spt spt | BS spt 'a spt
```

The taggable `cakeml` declaration is the abbreviation `num_set = unit spt`, which
`Misc.Sptree.NumSet` matches by construction.

`Misc.Sptree.sptLookup`, `Misc.Sptree.sptInsert`, `Misc.Sptree.sptIsEmpty` and
`Misc.Sptree.sptWf` mirror the HOL `lookup`, `insert`, `isEmpty` (i.e. `t = LN`)
and `wf` definitions, including the recursive key arithmetic
`(k - 1) DIV 2` and the `EVEN k` branch selection.  `EVEN` is rendered as
`k % 2 = 0` in Lean.  The recursion is written so that the recursive call sits in
each parity branch on a direct subterm, which makes the equations hold
definitionally (as Lean structural recursion rather than HOL's
well-founded recursion).
-/

namespace Flapjack

/-- Exact Lean rendering of the HOL `spt` datatype
`spt = LN | LS 'a | BN spt spt | BS spt 'a spt`. -/
inductive Spt (α : Type) : Type where
  /-- `LN`: the leaf holding no value. -/
  | ln : Spt α
  /-- `LS a`: the leaf holding `a`. -/
  | ls (value : α) : Spt α
  /-- `BN t1 t2`: an internal node with no value. -/
  | bn (left right : Spt α) : Spt α
  /-- `BS t1 a t2`: an internal node holding `a`. -/
  | bs (left : Spt α) (value : α) (right : Spt α) : Spt α
  deriving Repr, DecidableEq

/-- The CakeML abbreviation `num_set = unit spt` (`cakeml/misc/miscScript.sml:787`). -/
@[hol "cakeml/misc/miscScript.sml" "num_set"]
abbrev NumSet : Type := Spt Unit

/-- HOL `sptree$isEmpty t = (t = LN)`. -/
def sptIsEmpty {α : Type} : Spt α → Bool
  | .ln => true
  | _ => false

/-- HOL `sptree$wf`: well-formedness (no internal node whose both children are empty). -/
def sptWf {α : Type} : Spt α → Bool
  | .ln => true
  | .ls _ => true
  | .bn left right => sptWf left && sptWf right && !(sptIsEmpty left && sptIsEmpty right)
  | .bs left _ right => sptWf left && sptWf right && !(sptIsEmpty left && sptIsEmpty right)

/-- HOL `sptree$lookup` with the recursive key arithmetic `(k - 1) DIV 2`. -/
def sptLookup {α : Type} (key : Nat) : Spt α → Option α
  | .ln => none
  | .ls value => if key = 0 then some value else none
  | .bn left right =>
      if key = 0 then none
      else if key % 2 = 0 then sptLookup ((key - 1) / 2) left
      else sptLookup ((key - 1) / 2) right
  | .bs left value right =>
      if key = 0 then some value
      else if key % 2 = 0 then sptLookup ((key - 1) / 2) left
      else sptLookup ((key - 1) / 2) right

/-- HOL `sptree$insert` with the recursive key arithmetic `(k - 1) DIV 2`. -/
def sptInsert {α : Type} (key : Nat) (value : α) : Spt α → Spt α
  | .ln =>
      if key = 0 then .ls value
      else if key % 2 = 0 then .bn (sptInsert ((key - 1) / 2) value .ln) .ln
      else .bn .ln (sptInsert ((key - 1) / 2) value .ln)
  | .ls existing =>
      if key = 0 then .ls value
      else if key % 2 = 0 then .bs (sptInsert ((key - 1) / 2) value .ln) existing .ln
      else .bs .ln existing (sptInsert ((key - 1) / 2) value .ln)
  | .bn left right =>
      if key = 0 then .bs left value right
      else if key % 2 = 0 then .bn (sptInsert ((key - 1) / 2) value left) right
      else .bn left (sptInsert ((key - 1) / 2) value right)
  | .bs left existing right =>
      if key = 0 then .bs left value right
      else if key % 2 = 0 then .bs (sptInsert ((key - 1) / 2) value left) existing right
      else .bs left existing (sptInsert ((key - 1) / 2) value right)

/-- `sptLookup` on the empty set is `none`. -/
@[simp] theorem sptLookup_ln {α : Type} (key : Nat) :
    sptLookup key (.ln : Spt α) = none := by simp [sptLookup]

/-- `sptIsEmpty` on the empty tree is `true`. -/
@[simp] theorem sptIsEmpty_ln {α : Type} : sptIsEmpty (.ln : Spt α) = true := by simp [sptIsEmpty]

/-- `sptWf` on the empty tree is `true`. -/
@[simp] theorem sptWf_ln {α : Type} : sptWf (.ln : Spt α) = true := by simp [sptWf]

/-- Inserting key `0` into the empty tree gives `LS value`. -/
@[simp] theorem sptInsert_ln_zero {α : Type} (value : α) :
    sptInsert 0 value (.ln : Spt α) = .ls value := by simp [sptInsert]

/-- Looking up key `0` after inserting it gives the inserted value. -/
theorem sptLookup_sptInsert_zero {α : Type} (value : α) (tree : Spt α) :
    sptLookup 0 (sptInsert 0 value tree) = some value := by
  cases tree <;> simp [sptInsert, sptLookup]

/-- Inserting key `0` overwrites any existing value at key `0`. -/
theorem sptLookup_sptInsert_zero_overwrite {α : Type} (first second : α) (tree : Spt α) :
    sptLookup 0 (sptInsert 0 second (sptInsert 0 first tree)) = some second := by
  cases tree <;> simp [sptInsert, sptLookup]

end Flapjack