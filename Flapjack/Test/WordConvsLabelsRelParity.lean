import Flapjack.Pancake.WordConvs

/-!
# Parity guards for `wordConvs$labels_rel`

Mirrors `scripts/hol-probes/word_convs_labels_rel_probe.out`, which simplifies
the same concrete HOL terms under `wordConvs$labels_rel_def`.

`labelsRel` is a `Prop` with a universal subset conjunct, so it has no
computable `Decidable` instance.  The `example`s below are the kernel-checked
parity statements; `labelsRelCheck` is the executable mirror used for the
`#guard`/runtime checks (same rows, same expected `true`/`false`).
-/

namespace Flapjack.Test.WordConvsLabelsRelParity

open Flapjack

private def natPairLists : List (Nat × Nat) := [(1, 2), (3, 4)]

/-- Executable mirror of `labelsRel` for concrete lists: the new labels must be
duplicate-free whenever the old ones are, and every new label must occur in the
old list. -/
private def labelsRelCheck {β} [BEq β] (old new : List β) : Bool :=
  (new.eraseDups.length == new.length || !(old.eraseDups.length == old.length)) &&
    new.all (fun label => old.contains label)

-- Kernel-checked parity statements, one per oracle row.
example : labelsRel ([1, 2] : List Nat) [1, 2] := by simp [labelsRel]
example : labelsRel ([1, 2] : List Nat) [1] := by simp [labelsRel]
example : ¬ labelsRel ([1] : List Nat) [1, 2] := by simp [labelsRel]
example : labelsRel ([1, 1] : List Nat) [1] := by simp [labelsRel]
example : ¬ labelsRel ([1, 2] : List Nat) [1, 1] := by simp [labelsRel]
example : labelsRel ([1] : List Nat) [] := by simp [labelsRel]
example : ¬ labelsRel ([] : List Nat) [1] := by simp [labelsRel]
example : labelsRel (([1, 2] ++ [3]) : List Nat) ([1] ++ []) := by simp [labelsRel]
example : labelsRel natPairLists [(1, 2)] := by simp [labelsRel, natPairLists]

-- Theorem applications, exercising the ported HOL equations.
example : labelsRel ([1, 2] : List Nat) [1, 2] := labelsRel_refl _
example : labelsRel ([1, 2] ++ [3] : List Nat) ([1] ++ []) :=
  labelsRel_append (xs := [1, 2]) (xs₁ := [1]) (ys := [3]) (ys₁ := [])
    (by simp [labelsRel]) (by simp [labelsRel])
example : labelsRel ([1, 2] : List Nat) [1] :=
  labelsRel_trans (labelsRel_refl _) (by simp [labelsRel])
example : labelsRel ([1, 2] : List Nat) [2, 1] :=
  labelsRel_of_perm (List.Perm.swap 1 2 [])
example : labelsRel ([1, 2] : List Nat) [1, 2] :=
  labelsRel_cons (labelsRel_refl _) (labelsRel_refl _)

def runChecks : IO Bool := do
  let reflOk := labelsRelCheck ([1, 2] : List Nat) [1, 2]
  let subsetOk := labelsRelCheck ([1, 2] : List Nat) [1]
  let supersetBad := !labelsRelCheck ([1] : List Nat) [1, 2]
  let dupOldOk := labelsRelCheck ([1, 1] : List Nat) [1]
  let dupNewBad := !labelsRelCheck ([1, 2] : List Nat) [1, 1]
  let emptyOk := labelsRelCheck ([1] : List Nat) []
  let nilBad := !labelsRelCheck ([] : List Nat) [1]
  let appendOk := labelsRelCheck (([1, 2] ++ [3]) : List Nat) ([1] ++ [])
  let pairOk := labelsRelCheck natPairLists [(1, 2)]
  let all := reflOk && subsetOk && supersetBad && dupOldOk && dupNewBad &&
    emptyOk && nilBad && appendOk && pairOk
  if all then
    IO.println "PASS wordConvs labels_rel refl/subset/append/perm guards"
  else
    IO.println "FAIL wordConvs labels_rel refl/subset/append/perm guards"
  pure all

end Flapjack.Test.WordConvsLabelsRelParity