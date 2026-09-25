import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.AssignPrimitiveExact
import Flapjack.Pancake.Semantics.PanSem.StoreExact
import Flapjack.Pancake.Semantics.PanSem.ReturnRaiseExact
import Flapjack.Pancake.Semantics.PanSem.TickShMemExact
import Flapjack.Pancake.Semantics.PanSem.ExtCallExact

/-!
# Exact-state dispatcher for reviewed nonrecursive PanSem clauses

This dispatcher assembles the reviewed clause definitions over the exact
`PanSemStateExact` / `ProgHOL` / `ExpHOL` carriers. It handles the
nonrecursive clauses whose exact helpers are available: `Skip`, `Assign`,
`Primitive`, the three stores, `ShMemLoad`, `ShMemStore`, `Break`, `Continue`,
`Return`, `Raise`, `Tick`, `ExtCall`, and `Annot`.

The outer `Option` means that a constructor has no assembled clause in this
fragment; it is distinct from the inner HOL result option. `Dec`, `Seq`, `If`,
`While`, `Call`, and `DecCall` remain open here. This fragment does not claim
the recursive HOL `evaluate_def` and has no `@[hol]` tag.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (ProgHOL)

/-- Dispatch exact `ProgHOL` constructors to their reviewed nonrecursive
    `evaluate_def` clauses. `none` marks a recursive or not-yet-reviewed
    constructor, rather than a HOL evaluation result. -/
def evalPanSemNonrecursiveHOLExact {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs] :
    Option (Option (PanSemResultExact width) × PanSemStateExact width σ) := by
  exact match program with
  | .skip => some (none, state)
  | .dec _ _ _ _ => none
  | .assign kind name source =>
      some (assignStepHOLExact state kind name source
        (fun _ expression => evalHOLExact state expression))
  | .primitive name operator arguments =>
      some (primitiveStepHOLExact state name operator arguments
        (fun _ expressions => evalListHOLExact state expressions))
  | .store address value =>
      some (storeStepHOLExact state address value
        (fun _ expression => evalHOLExact state expression))
  | .store32 address value =>
      some (store32StepHOLExact state address value
        (fun _ expression => evalHOLExact state expression))
  | .storeByte address value =>
      some (storeByteStepHOLExact state address value
        (fun _ expression => evalHOLExact state expression))
  | .seq _ _ => none
  | .ite _ _ _ => none
  | .while _ _ => none
  | .break => some (some .break, state)
  | .continue => some (some .continue, state)
  | .call _ _ _ => none
  | .decCall _ _ _ _ _ => none
  | .extCall function configuration configurationLength array arrayLength =>
      some (extCallStepHOLExact state
        (fun _ expression => evalHOLExact state expression)
        function configuration configurationLength array arrayLength)
  | .raise exception value =>
      some (raiseStepHOLExact state exception value
        (fun _ expression => evalHOLExact state expression))
  | .return value =>
      some (returnStepHOLExact state value
        (fun _ expression => evalHOLExact state expression))
  | .shMemLoad size kind name address =>
      some (shMemLoadClauseHOLExact state size kind name address
        (fun _ expression => evalHOLExact state expression))
  | .shMemStore size address value =>
      some (shMemStoreClauseHOLExact state size address value
        (fun _ expression => evalHOLExact state expression))
  | .tick => some (tickStepHOLExact state)
  | .annot _ _ => some (none, state)

end Flapjack
