import Flapjack.Compiler.Backend.WordToStack.Proofs.NativeAccessors
import Flapjack.Compiler.Backend.Parmove.Semantics
import Flapjack.Misc.FindIndex.ShiftZero
import Lean.Elab.Tactic.Omega

namespace Flapjack.WordToStackProofs.MoveAuxStep
open Flapjack.Compiler.Backend.Parmove Flapjack.Misc

/-- Flapjack grouping of the exact scratch-read ordering guard in original
 evaluate_wMoveAux_seqsem. This is proof infrastructure, not a standalone HOL
 declaration, and makes no global scheduler safety assertion. -/
def ScratchReady {β : Type} (moves : List (Option Nat × Option Nat))
    (env : Option Nat → Option β) : Prop :=
  match findIndex none (moves.map Prod.snd) 0 with
  | none => True
  | some i =>
    match findIndex none (moves.map Prod.fst) 0 with
    | none => (env none).isSome = true
    | some j => i ≤ j → (env none).isSome = true

/-- Flapjack inline source proof: an actual successful scratch lookup satisfies
 every optional first-index guard, with no move-list validity restriction. -/
theorem scratchReadyOfSome {β : Type} (moves : List (Option Nat × Option Nat))
    (env : Option Nat → Option β) (found : (env none).isSome = true) :
    ScratchReady moves env := by
  unfold ScratchReady
  split
  · trivial
  · split
    · exact found
    · intro _; exact found

/-- Flapjack inline source proof: a head scratch read precedes every possible
first write, so the original guard forces its actual lookup to succeed. -/
theorem headScratchRead {β : Type} (destination : Option Nat)
    (moves : List (Option Nat × Option Nat)) (env : Option Nat → Option β)
    (ready : ScratchReady ((destination,none)::moves) env) : (env none).isSome = true := by
  cases destination with
  | none => simpa [ScratchReady,findIndex] using ready
  | some destination =>
    simp only [ScratchReady,List.map_cons,findIndex,Option.some_ne_none,↓reduceIte] at ready
    cases found : findIndex none (moves.map Prod.fst) 1 with
    | none => simpa [found] using ready
    | some j => exact (by simpa [found] using ready : 0≤j → (env none).isSome=true) (Nat.zero_le j)

/-- Flapjack inline original induction guard descent. The successful head
lookup is obtained from the original getVars/environment guards in the full
simulation; no target execution or postrelation is assumed here. -/
theorem scratchReadyTail {β : Type} (destination source : Option Nat)
    (moves : List (Option Nat × Option Nat)) (env : Option Nat → Option β)
    (ready : ScratchReady ((destination,source)::moves) env)
    (headRead : (env source).isSome = true) :
    ScratchReady moves (updateEnv env destination (env source)) := by
  cases destination with
  | none =>
    apply scratchReadyOfSome
    simpa [updateEnv] using headRead
  | some destination =>
    cases source with
    | none =>
      apply scratchReadyOfSome
      simpa [updateEnv] using headScratchRead (some destination) moves env ready
    | some source =>
      simp only [ScratchReady,List.map_cons,findIndex,Option.some_ne_none,↓reduceIte] at ready
      rw [findIndexShiftZero (moves.map Prod.snd) none 1,
        findIndexShiftZero (moves.map Prod.fst) none 1] at ready
      unfold ScratchReady
      cases read : findIndex none (moves.map Prod.snd) 0 <;>
        cases write : findIndex none (moves.map Prod.fst) 0 <;>
        simp_all [updateEnv]

/-- Flapjack grouping of the original real-source register list. The getD0
 default is used only below the isSome filter, hence never observes NONE. -/
def realSources (moves : List (Option Nat × Option Nat)) : List Nat :=
  ((moves.map Prod.snd).filter Option.isSome).map (fun x => 2*x.getD 0)

/-- Flapjack inline original head-read derivation from the entire original
source-success and environment correspondence guards. This supplies the head
value internally rather than assuming target execution succeeds. -/
theorem actualHeadRead {width : Nat} [NeZero width] {C F : Type}
    (destination source : Option Nat) (moves : List (Option Nat × Option Nat))
    (state : WordSemStateFiniteExact width C F) (env : Option Nat → Option (WordLocW width))
    (correspondence : ∀ i value, env (some i)=some value ↔
      WordSemStateFiniteExact.getVar (2*i) state=some value)
    (reads : (WordSemStateFiniteExact.getVars (realSources ((destination,source)::moves)) state).isSome=true)
    (ready : ScratchReady ((destination,source)::moves) env) :
    (env source).isSome=true := by
  cases source with
  | none => exact headScratchRead destination moves env ready
  | some source =>
    have allReads := NativeWordAccessors.isSomeGetVarsEvery _ state |>.mp reads
    have found := allReads (2*source) (by simp [realSources])
    cases lookup : WordSemStateFiniteExact.getVar (2*source) state with
    | none => simp [lookup] at found
    | some value => simp [show env (some source)=some value from (correspondence source value).mpr lookup]

/-- Flapjack inline original source/environment update correspondence. The
 actual head read is derived above, and source setVar is exactly the original
 optional destination operation; all real register observations are retained. -/
theorem updatedCorrespondence {width : Nat} [NeZero width] {C F : Type}
    (destination source : Option Nat) (state : WordSemStateFiniteExact width C F)
    (env : Option Nat → Option (WordLocW width)) (value : WordLocW width)
    (correspondence : ∀ i v, env (some i)=some v ↔
      WordSemStateFiniteExact.getVar (2*i) state=some v)
    (read : env source=some value) :
    ∀ i v, updateEnv env destination (env source) (some i)=some v ↔
      WordSemStateFiniteExact.getVar (2*i)
        (match destination with | none => state | some y => WordSemStateFiniteExact.setVar (2*y) value state)=some v := by
  intro i v
  cases destination with
  | none => simpa [updateEnv] using correspondence i v
  | some y =>
    by_cases same : i=y
    · subst i
      simp [updateEnv,read,WordSemStateFiniteExact.getVar,WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_same]
    · have different : 2*i≠2*y := by omega
      simpa [updateEnv,same,WordSemStateFiniteExact.getVar,WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_ne _ _ _ _ different] using correspondence i v

/-- Flapjack inline original tail source-success guard. Real tail sources are
already in the original successful head/tail read list, and a source variable
update cannot turn any present lookup into NONE. No final values are assumed. -/
theorem tailReads {width : Nat} [NeZero width] {C F : Type}
    (destination source : Option Nat) (moves : List (Option Nat × Option Nat))
    (state : WordSemStateFiniteExact width C F) (value : WordLocW width)
    (reads : (WordSemStateFiniteExact.getVars (realSources ((destination,source)::moves)) state).isSome=true) :
    (WordSemStateFiniteExact.getVars (realSources moves)
      (match destination with | none => state | some y => WordSemStateFiniteExact.setVar (2*y) value state)).isSome=true := by
  have original : (WordSemStateFiniteExact.getVars (realSources moves) state).isSome=true := by
    apply (NativeWordAccessors.isSomeGetVarsEvery _ state).mpr
    intro n member
    apply (NativeWordAccessors.isSomeGetVarsEvery _ state).mp reads n
    cases source with
    | none => simpa [realSources] using member
    | some source =>
      simp [realSources] at member ⊢
      exact Or.inr member
  cases destination with
  | none => exact original
  | some y => exact NativeWordAccessors.isSomeGetVarsSetVar _ state (2*y) value original

end Flapjack.WordToStackProofs.MoveAuxStep
