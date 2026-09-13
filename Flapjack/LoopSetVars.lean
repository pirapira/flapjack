import Flapjack.LoopSemantics

/-!
Faithful port of the original Pancake Loop `set_var` / `set_vars`.

Source reference:
`cakeml/pancake/semantics/loopSemScript.sml:108-116`

```
set_var v x s = s with locals := insert v x s.locals
set_vars vs xs s = s with locals := alist_insert vs xs s.locals
```

The original `alist_insert` (`cakeml/.../sptreeScript.sml:2085-2089`) inserts the
pair list from the tail towards the head, so the *first* occurrence of a
repeated name wins; a shorter value list truncates silently.  This is the
opposite of `Flapjack.loopAssignValues`
(`Flapjack/LoopSemantics.lean:1451`), whose `List.zip`-then-`foldl` makes the
last occurrence win.  This file ports the original ordering directly.
-/

namespace Flapjack

/-- Look up a key in an association list, first occurrence winning. -/
def lookupFirst (key : Nat) : List (Nat × α) → Option α
  | [] => none
  | (name, value) :: rest => if key = name then some value else lookupFirst key rest

/-- The original `alist_insert`: overlay a first-occurrence-wins association
    list onto a base local environment. -/
def loopSetVars (locals : Nat → Option α) (names : List Nat) (values : List α) :
    Nat → Option α :=
  fun current =>
    match lookupFirst current (names.zip values) with
    | some value => some value
    | none => locals current

/-- `set_var` from `loopSemScript.sml:108-109`. -/
def loopSetVar (locals : Nat → Option α) (name : Nat) (value : α) : Nat → Option α :=
  fun current => if current = name then some value else locals current

theorem loopSetVar_eq_updateLoopLocal (locals : Nat → Option α) (name : Nat)
    (value : α) :
    loopSetVar locals name value = updateLoopLocal locals name value :=
  rfl

theorem lookupFirst_of_absent (key : Nat) (entries : List (Nat × α))
    (absent : ∀ entry, entry ∈ entries → entry.1 ≠ key) :
    lookupFirst key entries = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      have hne : key ≠ entry.1 := fun h => absent entry (by simp) h.symm
      simp only [lookupFirst, hne, if_false]
      exact ih (fun e he => absent e (by simp [he]))

/-- First-occurrence-wins: a key that appears at the head with value `value`
    reads back as `value` regardless of later duplicate entries. -/
theorem loopSetVars_head_wins (locals : Nat → Option α) (name : Nat) (value : α)
    (names : List Nat) (values : List α) :
    loopSetVars locals (name :: names) (value :: values) name = some value := by
  simp [loopSetVars, lookupFirst]

/-- A key untouched by the overlay reads back from the base environment. -/
theorem loopSetVars_of_not_mem (locals : Nat → Option α) (names : List Nat)
    (values : List α) (key : Nat)
    (absent : ∀ entry, entry ∈ names.zip values → entry.1 ≠ key) :
    loopSetVars locals names values key = locals key := by
  simp [loopSetVars, lookupFirst_of_absent key (names.zip values) absent]

end Flapjack
