import Flapjack.RiscV.RegisterMap

/-!
# CakeML IRC allocator core for frame occupancy (analysis slice)

This module ports the pure, frame-relevant core of CakeML's register
allocators, taken from the original developer sources:

* `cakeml/compiler/backend/reg_alloc/reg_allocScript.sml`
* `cakeml/compiler/backend/word_allocScript.sml`

It is the allocator-core slice for bead `flapjack-pxn.8.5.14.1.3.1` ("Port
Cake IRC register-allocation core for frame parity").  It is deliberately
independent of the Word-to-Stack frame numbering and of the GC-live bitmap
list, so that the integration slice (`flapjack-pxn.8.5.14.1.3`, owned by
flapjack-four) can reuse these decisions without duplicating them.

The Cake frame policy is decided by exactly these ingredients:

* the WordLang variable convention (`is_phy_var` / `is_alloc_var` /
  `is_stack_var`), which distinguishes hardware registers, allocatable
  registers and forced stack variables;
* `merge_stack_only` / `merge_stack_sets` / `remove_temp_stack`, which
  compute the set of stack-only ("forced stack") variables from the move
  graph and the clash tree (i.e. which source values, saved registers and
  call return-address temporaries must occupy frame slots);
* `get_spillcost` / `get_coalescecost`, the IRC spill and coalescing costs;
* `get_forced`, the hardware-forced interference edges (on RISC-V, the
  `AddCarry`/`AddOverflow`/`SubOverflow`/`LongMul` operand pairs);
* `limit_var`, which fixes the numbering base for the fresh SSA temporaries
  emitted by `full_ssa_cc_trans` and therefore the temporary slot numbers
  seen by the allocator.

The remaining data structures of the HOL development (sptrees, the mutable
interference graph and the worklist machine) are intentionally not ported
here; this slice exposes their frame-relevant decision functions only.

There is no Mathlib dependency in the `Flapjack.RiscV` subtree, so the
sets are represented by membership lists and the arithmetic is verified with
core tactics.
-/

namespace Flapjack.RiscV.CakeAlloc

/-! ## WordLang variable convention

`reg_allocScript.sml:1132-1140`:

```
is_stack_var n = (n MOD 4 = 3)
is_phy_var   n = (n MOD 2 = 0)
is_alloc_var n = (n MOD 4 = 1)
```

Evens are physical (hardware) registers, `4n+1` are allocatable registers and
`4n+3` are stack registers. -/

/-- A WordLang variable is a physical (hardware) register when it is even. -/
def isPhyVar (n : Nat) : Bool := n % 2 == 0

/-- A WordLang variable is an allocatable register when `n % 4 = 1`. -/
def isAllocVar (n : Nat) : Bool := n % 4 == 1

/-- A WordLang variable is a stack variable when `n % 4 = 3`. -/
def isStackVar (n : Nat) : Bool := n % 4 == 3

/-- The three conventions partition the WordLang variable space
(HOL `convention_partitions`, `reg_allocScript.sml:1142-1156`). -/
theorem convention_partitions (n : Nat) :
    (isStackVar n = true ↔ isPhyVar n = false ∧ isAllocVar n = false) ∧
    (isPhyVar n = true ↔ isStackVar n = false ∧ isAllocVar n = false) ∧
    (isAllocVar n = true ↔ isPhyVar n = false ∧ isStackVar n = false) := by
  have hlt : n % 4 < 4 := Nat.mod_lt n (by decide)
  have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have h2eq : n % 2 = n % 4 % 2 := (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)).symm
  rcases hcases with h | h | h | h <;>
    simp [isStackVar, isAllocVar, isPhyVar, h, h2eq]

/-! ## Membership-list sets

The HOL development uses `sptree$num_set` (a set of `num`).  Because the
`Flapjack.RiscV` subtree has no Mathlib, `num_set` operations are modelled
here as membership lists with set semantics. -/

/-- Insert into a membership set (`sptree$insert`). -/
def insertSet (a : Nat) (s : List Nat) : List Nat :=
  if s.contains a then s else a :: s

/-- Delete from a membership set (`sptree$delete`). -/
def deleteSet (a : Nat) (s : List Nat) : List Nat := s.erase a

/-- Union of membership sets (`sptree$union`). -/
def unionSet (s t : List Nat) : List Nat :=
  s ++ t.filter (fun a => !s.contains a)

/-- Intersection of membership sets (`sptree$inter`). -/
def interSet (s t : List Nat) : List Nat := s.filter (fun a => t.contains a)

/-- Difference of membership sets (`sptree$difference`). -/
def diffSet (s t : List Nat) : List Nat := s.filter (fun a => !t.contains a)

/-! ## Stack-only propagation

`merge_stack_only` (`word_allocScript.sml:1711-1725`) propagates the
stack-only decision along a move `x <- y`:

```
merge_stack_only (x,y) (ts,fs) =
  if lookup x ts = SOME () then
    (ts + y if is_alloc_var y, fs + x if not is_phy_var y)
  else if is_stack_var x then
    (ts + y if is_alloc_var y, fs)
  else (delete y ts, fs)
``` -/

/-- Propagate the stack-only decision along a single move (`x <- y`). -/
def mergeStackOnly (x y : Nat) (ts fs : List Nat) : List Nat × List Nat :=
  if ts.contains x then
    ((if isAllocVar y then insertSet y ts else ts),
     (if isPhyVar y then fs else insertSet x fs))
  else if isStackVar x then
    ((if isAllocVar y then insertSet y ts else ts), fs)
  else
    (deleteSet y ts, fs)

/-- Merge the stack-only sets of two branches
(`merge_stack_sets`, `word_allocScript.sml:1727-1732`). -/
def mergeStackSets (ts _fs tsL fsL tsR fsR : List Nat) : List Nat × List Nat :=
  let keep1 := interSet tsR (interSet tsL ts)
  let keep2 := unionSet (diffSet tsL ts) (diffSet tsR ts)
  (unionSet keep1 keep2, unionSet fsL fsR)

/-- Remove temporary names from the stack-only set
(`remove_temp_stack`, `word_allocScript.sml:1734-1737`). -/
def removeTempStack (names : List Nat) (ts fs : List Nat) : List Nat × List Nat :=
  (names.foldr deleteSet ts, fs)

/-! ## IRC costs

`get_spillcost` (`word_allocScript.sml:1666-1670`) and `get_coalescecost`
(`word_allocScript.sml:1676-1681`) use CakeML's fixed magic numbers. -/

/-- CakeML spill cost from the (cut, left-reg, left-mem, right-reg, right-mem)
counts and the tail-position flag. -/
def getSpillCost (c lr lm rr rm : Nat) (isTail : Bool) : Nat :=
  (c + 2 * lr + 4 * lm + 2 * rr + 4 * rm) * (if isTail then 5 else 1)

/-- CakeML coalescing cost for a canonicalised move `(n, p, (x, y))`, given an
optional spill-cost table. -/
def getCoalesceCost (spillCost : Nat → Option Nat) (n p x y : Nat) : Nat × (Nat × Nat) :=
  let xcost := if (spillCost x).isSome then 1 else 0
  let ycost := if (spillCost y).isSome then 1 else 0
  (n * (10 * (p + 1) + xcost + ycost), (x, y))

/-! ## Hardware-forced edges

For RISC-V `get_forced` (`word_allocScript.sml:1466-1513`) adds the operand
pairs that share an encoding register.  `AddCarry r1 r2 r3 r4` forces
`(r1, r3)` and `(r1, r4)`; `AddOverflow`/`SubOverflow` force `(r1, r3)`; and
`LongMul r1 r2 r3 r4` forces `(r1, r3)` and `(r1, r4)`. -/

/-- The RISC-V forced pairs contributed by `AddCarry r1 _ r3 r4`. -/
def getForcedAddCarry (r1 r3 r4 : Nat) : List (Nat × Nat) :=
  (if r1 = r3 then [] else [(r1, r3)]) ++
    (if r1 = r4 then [] else [(r1, r4)])

/-- The RISC-V forced pair contributed by `AddOverflow r1 _ r3 _` or
`SubOverflow r1 _ r3 _`. -/
def getForcedOverflow (r1 r3 : Nat) : List (Nat × Nat) :=
  if r1 = r3 then [] else [(r1, r3)]

/-- The RISC-V forced pairs contributed by `LongMul r1 _ r3 r4`. -/
def getForcedLongMul (r1 r3 r4 : Nat) : List (Nat × Nat) :=
  (if r1 = r3 then [] else [(r1, r3)]) ++
    (if r1 = r4 then [] else [(r1, r4)])

/-! ## Temporary numbering

`limit_var` (`word_allocScript.sml:1816-1820`) fixes the numbering base for the
fresh SSA temporaries created by `full_ssa_cc_trans`; it is the smallest
multiple of four strictly above `max_var`, plus one. -/

/-- The numbering limit used for the fresh SSA temporaries. -/
def limitVar (x : Nat) : Nat := x + (4 - x % 4) + 1

/-! ## Colouring defaults

`sp_default` (`reg_allocScript.sml:1219-1222`) and `total_colour`
(`word_allocScript.sml:1592-1595`) turn the allocator colouring into concrete
register numbers: physical variables keep their hardware register, allocatable
variables get `2 * colour` and uncoloured variables default to zero. -/

/-- Default colour lookup for a variable name (`sp_default`): an allocated
variable keeps its colour, a physical variable maps to its hardware register
`n / 2`, and everything else defaults to `0`. -/
def spDefault (colour : List (Nat × Nat)) (n : Nat) : Nat :=
  match colour.find? (fun entry => entry.1 == n) with
  | some entry => entry.2
  | none => if isPhyVar n then n / 2 else 0

/-- Concrete register number for a variable name under a colouring. -/
def totalColour (colour : List (Nat × Nat)) (n : Nat) : Nat :=
  2 * spDefault colour n

end Flapjack.RiscV.CakeAlloc
