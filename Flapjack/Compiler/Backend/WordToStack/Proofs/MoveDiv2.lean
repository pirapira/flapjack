import Flapjack.Compiler.Backend.Parmove.MapInj
import Flapjack.Compiler.Backend.Parmove.ParseSemMapInj
import Flapjack.Compiler.Backend.Parmove.DestinationWrapper
import Flapjack.Compiler.Backend.WordToStack.Proofs.LiveListSupport

namespace Flapjack.Compiler.Backend.WordToStack
open Flapjack.Compiler.Backend.Parmove

/-- Flapjack list infrastructure for the original IS_SOME-filtered scheduler
observations. No separate HOL declaration names this concrete list identity. -/
private theorem filterSomeMap (xs : List (Option Nat)) (f : Nat → Nat) :
    ((xs.map (Option.map f)).filter Option.isSome) =
      (xs.filter Option.isSome).map (Option.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [ih]

/-- Flapjack derivation of the source-restricted halving injection required by
the accepted scheduler renaming theorem; it introduces no global injection. -/
private theorem endpointEven (moves : List (Nat × Nat))
    (evenDest : ∀ n ∈ moves.map Prod.fst, n % 2 = 0)
    (evenSrc : ∀ n ∈ moves.map Prod.snd, n % 2 = 0) :
    ∀ n ∈ moves.map Prod.fst ++ moves.map Prod.snd, n % 2 = 0 := by
  intro n h
  exact (List.mem_append.mp h).elim (evenDest n) (evenSrc n)

/-- Full original local scheduled-destination reconstruction. THE is rendered
by getD 0 only beneath FILTER IS_SOME, so its none default is unobservable. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "TIMES2_DIV2_lemma"]
theorem times2Div2Lemma (moves : List (Nat × Nat))
    (valid : windmill moves)
    (evenDest : ∀ n ∈ moves.map Prod.fst, n % 2 = 0)
    (evenSrc : ∀ n ∈ moves.map Prod.snd, n % 2 = 0) :
    (((parmove (moves.map (Prod.map (· / 2) (· / 2)))).map Prod.fst).filter Option.isSome).map
      (fun x => 2 * x.getD 0) =
    (((parmove moves).map Prod.fst).filter Option.isSome).map (fun x => x.getD 0) := by
  have even := endpointEven moves evenDest evenSrc
  have rename := parmove_MAP_INJ (f := fun n : Nat => n / 2) (ls := moves)
    ⟨by dsimp; intro x y h; exact evenDiv2Inj x y (even x h.1) (even y h.2.1) h.2.2, valid⟩
  rw [rename]
  simp only [List.map_map, Function.comp_def, Prod.map_fst]
  rw [show (List.map (fun x : Move Nat => Option.map (· / 2) x.1) (parmove moves)) =
      ((parmove moves).map Prod.fst).map (Option.map (· / 2)) by simp]
  rw [filterSomeMap, List.map_map]
  apply List.map_congr_left
  intro x member
  obtain ⟨member, someX⟩ := List.mem_filter.mp member
  cases x with
  | none => simp at someX
  | some n =>
    have hn := evenDest n (memMapFstParmove moves n member)
    simp only [Function.comp_def, Option.map_some, Option.getD_some]
    omega

/-- Full original local parallel-value reconstruction at every scheduled real
 destination. The environment carrier remains arbitrary, as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "parsem_parmove_DIV2_lemma"]
theorem parsemParmoveDiv2Lemma {β : Type} (moves : List (Nat × Nat)) (r : Option Nat → β)
    (valid : windmill moves)
    (evenDest : ∀ n ∈ moves.map Prod.fst, n % 2 = 0)
    (evenSrc : ∀ n ∈ moves.map Prod.snd, n % 2 = 0) :
    (((parmove (moves.map (Prod.map (· / 2) (· / 2)))).map Prod.fst).filter Option.isSome).map
      (parsem ((moves.map (Prod.map (· / 2) (· / 2))).map (Prod.map some some)) r) =
    (((parmove moves).map Prod.fst).filter Option.isSome).map
      (parsem (moves.map (Prod.map some some)) (r ∘ Option.map (· / 2))) := by
  have even := endpointEven moves evenDest evenSrc
  have rename := parmove_MAP_INJ (f := fun n : Nat => n / 2) (ls := moves)
    ⟨by dsimp; intro x y h; exact evenDiv2Inj x y (even x h.1) (even y h.2.1) h.2.2, valid⟩
  rw [rename]
  simp only [List.map_map, Function.comp_def, Prod.map_fst]
  rw [show (List.map (fun x : Move Nat => Option.map (· / 2) x.1) (parmove moves)) =
      ((parmove moves).map Prod.fst).map (Option.map (· / 2)) by simp]
  rw [filterSomeMap, List.map_map]
  apply List.map_congr_left
  intro x member
  obtain ⟨member, someX⟩ := List.mem_filter.mp member
  cases x with
  | none => simp at someX
  | some n =>
    have hn := memMapFstParmove moves n member
    let optional := moves.map (Prod.map some some)
    have optionalValid : windmill optional := by
      simpa [optional, windmill, List.map_map, Function.comp_def] using
        valid.map (f := Option.some) (by intro a b h; exact Option.some.inj h)
    have optionalEven : ∀ n, some n ∈ optional.map Prod.fst ++ optional.map Prod.snd → n % 2 = 0 := by
      intro n h
      have originalMember : n ∈ moves.map Prod.fst ++ moves.map Prod.snd := by
        simpa [optional, List.map_map, Function.comp_def] using h
      exact even n originalMember
    have injective : ∀ a ∈ optional.map Prod.fst ++ optional.map Prod.snd,
        ∀ b ∈ optional.map Prod.fst ++ optional.map Prod.snd,
          Option.map (· / 2) a = Option.map (· / 2) b → a = b := by
      intro a ha b hb eq
      cases a with
      | none => cases b <;> simp_all
      | some a =>
        cases b with
        | none => simp at eq
        | some b =>
          apply congrArg some
          exact evenDiv2Inj a b (optionalEven a ha) (optionalEven b hb) (by simpa using eq)
    have result := parsemMapInj optional (Option.map (· / 2)) r optionalValid injective
      (some n) (by simpa [optional, List.map_map, Function.comp_def] using hn)
    simpa [optional, List.map_map, Function.comp_def, Prod.map] using result

end Flapjack.Compiler.Backend.WordToStack
