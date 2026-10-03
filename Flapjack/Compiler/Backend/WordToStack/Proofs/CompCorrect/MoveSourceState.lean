import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Move
import Flapjack.Misc.Sptree.AlistInsertReverse

namespace Flapjack.WordToStackProofs.CompCorrect.Move
open Flapjack.Compiler.Backend.Parmove
open Flapjack.WordAlloc

/-- HOL inhabitedness for the existing option THE; no new default is defined. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Flapjack original Move inline reversal step. Native complete state equality
is proved under the original real-destination distinctness guard, on arbitrary
trees. This is inline proof factoring, not a separate HOL declaration. -/
theorem scheduledPostUnreverse {width : Nat} [NeZero width] {C F : Type}
    (scheduled : List (Option Nat × Option Nat))
    (env : Option Nat → Option (WordLocW width)) (source : WordSemStateFiniteExact width C F)
    (distinct : ((scheduled.map Prod.fst).filter Option.isSome).Nodup) :
    MoveAuxReconstruction.sourcePost scheduled env source =
      WordSemStateFiniteExact.setVars
        (((scheduled.map Prod.fst).filter Option.isSome).map (fun x => 2*holThe x))
        (((scheduled.map Prod.fst).filter Option.isSome).map (fun x => holThe (seqsem scheduled env x))) source := by
  have keyDistinct :
      (((scheduled.map Prod.fst).filter Option.isSome).map (fun x => 2*holThe x)).Nodup := by
    apply distinct.map_on
    intro x hx y hy equal
    have xs := (List.mem_filter.mp hx).2
    have ys := (List.mem_filter.mp hy).2
    cases x with
    | none => simp at xs
    | some x =>
      cases y with
      | none => simp at ys
      | some y =>
        apply congrArg some
        simp only [holThe] at equal
        omega
  simp only [MoveAuxReconstruction.sourcePost,MoveAuxReconstruction.destinations,
    List.map_reverse,List.filter_reverse]
  unfold WordSemStateFiniteExact.setVars
  rw [Flapjack.Misc.SptreeAlistInsertReverse.alistInsertReverse _ _ source.locals keyDistinct
    (by simp)]

/-- Flapjack original Move inline seqsem-to-parsem substitution, retaining the
whole source state rather than assuming the equality to be established. -/
theorem scheduledPostParallel {width : Nat} [NeZero width] {C F : Type}
    (moves : List (Nat × Nat)) (env : Option Nat → Option (WordLocW width))
    (source : WordSemStateFiniteExact width C F) (valid : windmill moves) :
    MoveAuxReconstruction.sourcePost (parmove moves) env source =
      WordSemStateFiniteExact.setVars
        ((((parmove moves).map Prod.fst).filter Option.isSome).map (fun x => 2*holThe x))
        ((((parmove moves).map Prod.fst).filter Option.isSome).map
          (fun x => holThe (parsem (moves.map (Prod.map some some)) env x))) source := by
  rw [scheduledPostUnreverse _ env source (allDistinctParmove moves valid)]
  have equivalent := parmove_correct moves valid env
  congr 1
  apply List.map_congr_left
  intro x member
  have real := (List.mem_filter.mp member).2
  rw [equivalent x real]
  rfl

/-- Flapjack original Move inline association observation for a parallel move
with original distinct destinations. The arbitrary environment is retained. -/
theorem parallelLookup {β : Type} (moves : List (Nat × Nat))
    (env : Option Nat → β) (key : Nat) (distinct : (moves.map Prod.fst).Nodup) :
    parsem (moves.map (Prod.map some some)) env (some key) =
      match keyLookup moves key with | none => env (some key) | some src => env (some src) := by
  induction moves with
  | nil => rfl
  | cons move moves ih =>
    rcases move with ⟨dst,src⟩
    have parts : dst ∉ moves.map Prod.fst ∧ (moves.map Prod.fst).Nodup := by simpa using distinct
    have fresh : some dst ∉ (moves.map (Prod.map some some)).map Prod.fst := by
      simpa [List.map_map,Function.comp_def] using parts.1
    simp only [List.map_cons,Prod.map]
    rw [parsem_cons (some dst) (some src) _ env fresh]
    by_cases same : key=dst
    · subst key
      simp [updateEnv,keyLookup,holAlookup]
    · simp only [updateEnv,Option.some.injEq,if_neg same]
      rw [ih parts.2]
      simp [keyLookup,holAlookup,Ne.symm same]

/-- Flapjack first-match observation: membership in the source destination
list supplies an actual association result, even when other keys duplicate. -/
theorem lookupPresent (moves : List (Nat × Nat)) (key : Nat)
    (member : key ∈ moves.map Prod.fst) : ∃ src, keyLookup moves key=some src := by
  induction moves with
  | nil => simp at member
  | cons move moves ih =>
    rcases move with ⟨dst,src⟩
    by_cases same : dst=key
    · subst dst; exact ⟨src,by simp [keyLookup,holAlookup]⟩
    · have tail : key ∈ moves.map Prod.fst := by simpa [Ne.symm same] using member
      obtain ⟨value,found⟩ := ih tail
      exact ⟨value,by simpa [keyLookup,holAlookup,same] using found⟩

/-- Flapjack filtered THE identity: the arbitrary NONE default is never
observed because every selected option is SOME. -/
theorem filteredTheMap (options : List (Option Nat)) (f : Nat → Nat) :
    (options.filter Option.isSome).map (fun x => f (holThe x)) =
      (options.filter Option.isSome).map (fun x => f (x.getD 0)) := by
  apply List.map_congr_left
  intro x member
  have real := (List.mem_filter.mp member).2
  cases x with
  | none => simp at real
  | some n => rfl

/-- Flapjack original Move complete-state halving reconstruction, before the
final actual operand association observation. All original even endpoints and
windmill guards are preserved; actual parmove correctness is used internally. -/
theorem scheduledPostDiv2 {width : Nat} [NeZero width] {C F : Type}
    (moves : List (Nat × Nat)) (env : Option Nat → Option (WordLocW width))
    (source : WordSemStateFiniteExact width C F) (valid : windmill moves)
    (evenDest : ∀ n ∈ moves.map Prod.fst, n % 2=0)
    (evenSrc : ∀ n ∈ moves.map Prod.snd, n % 2=0) :
    MoveAuxReconstruction.sourcePost (parmove (moves.map (Prod.map (· /2) (· /2)))) env source =
      WordSemStateFiniteExact.setVars
        ((((parmove moves).map Prod.fst).filter Option.isSome).map holThe)
        ((((parmove moves).map Prod.fst).filter Option.isSome).map
          (fun x => holThe (parsem (moves.map (Prod.map some some))
            (env ∘ Option.map (· /2)) x))) source := by
  rw [scheduledPostParallel _ env source (halvedWindmill moves valid evenDest)]
  have keys := Flapjack.Compiler.Backend.WordToStack.times2Div2Lemma moves valid evenDest evenSrc
  have values := Flapjack.Compiler.Backend.WordToStack.parsemParmoveDiv2Lemma moves env valid evenDest evenSrc
  have valueThe := congrArg (List.map holThe) values
  simp only [List.map_map,Function.comp_def] at valueThe
  have keyThe :
      ((((parmove (moves.map (Prod.map (· /2) (· /2)))).map Prod.fst).filter Option.isSome).map
        (fun x => 2*holThe x)) =
      ((((parmove moves).map Prod.fst).filter Option.isSome).map holThe) := by
    rw [filteredTheMap _ (fun x => 2*x),keys]
    simpa only [Function.id_def] using (filteredTheMap ((parmove moves).map Prod.fst) id).symm
  rw [keyThe]
  simp only [List.map_map,Function.comp_def]
  rw [valueThe]

/-- Flapjack actual association membership, with duplicates allowed. -/
theorem lookupMember (moves : List (Nat × Nat)) (key value : Nat)
    (found : keyLookup moves key=some value) : (key,value) ∈ moves := by
  induction moves with
  | nil => simp [keyLookup,holAlookup] at found
  | cons move moves ih =>
    rcases move with ⟨dst,src⟩
    by_cases same : dst=key
    · subst dst
      simp [keyLookup,holAlookup] at found
      subst src
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih (by simpa [keyLookup,holAlookup,same] using found))

/-- Flapjack original Move inline actual operand correspondence. A scheduled
real destination has an actual source association; source parity discharges
the halved read without assuming the desired value equality. -/
theorem parallelSourceValue {width : Nat} [NeZero width] {C F : Type}
    (moves : List (Nat × Nat)) (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (k key : Nat)
    (distinct : (moves.map Prod.fst).Nodup)
    (evenSrc : ∀ n ∈ moves.map Prod.snd, n % 2=0) (member : key ∈ moves.map Prod.fst) :
    holThe (parsem (moves.map (Prod.map some some))
      (moveEnv k source target ∘ Option.map (· /2)) (some key)) =
    holThe (WordSemStateFiniteExact.getVar (holThe (keyLookup moves key)) source) := by
  obtain ⟨src,found⟩ := lookupPresent moves key member
  have actual := lookupMember moves key src found
  have parity := evenSrc src (List.mem_map.mpr ⟨(key,src),actual,rfl⟩)
  have twice : 2*(src/2)=src := by omega
  rw [parallelLookup moves _ key distinct,found]
  simp only [Function.comp_def,Option.map_some,moveEnv,holThe,twice]

/-- Flapjack original Move inline whole source state reconstruction6220–6313.
The original source reads, distinct/even endpoints and locals well-formedness
(derived from the original state relation) suffice. All source fields are
retained; no desired source equality or target execution is a premise. -/
theorem scheduledSourceStateReconstruction {width : Nat} [NeZero width] {C F : Type}
    (moves : List (Nat × Nat)) (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (k : Nat) (values : List (WordLocW width))
    (distinct : (moves.map Prod.fst).Nodup)
    (evenDest : ∀ n ∈ moves.map Prod.fst, n % 2=0)
    (evenSrc : ∀ n ∈ moves.map Prod.snd, n % 2=0)
    (reads : WordSemStateFiniteExact.getVars (moves.map Prod.snd) source=some values)
    (wf : sptWf source.locals=true) :
    MoveAuxReconstruction.sourcePost (parmove (moves.map (Prod.map (· /2) (· /2))))
      (moveEnv k source target) source =
    WordSemStateFiniteExact.setVars (moves.map Prod.fst) values source := by
  rw [scheduledPostDiv2 moves _ source distinct evenDest evenSrc]
  have valueLists :
      ((((parmove moves).map Prod.fst).filter Option.isSome).map
        (fun x => holThe (parsem (moves.map (Prod.map some some))
          (moveEnv k source target ∘ Option.map (· /2)) x))) =
      ((((parmove moves).map Prod.fst).filter Option.isSome).map
        (fun x => holThe (WordSemStateFiniteExact.getVar
          (holThe (keyLookup moves (holThe x))) source))) := by
    apply List.map_congr_left
    intro x member
    obtain ⟨scheduled,real⟩ := List.mem_filter.mp member
    cases x with
    | none => simp at real
    | some key =>
      exact parallelSourceValue moves source target k key distinct evenSrc
        (memMapFstParmove moves key scheduled)
  rw [valueLists]
  unfold WordSemStateFiniteExact.setVars
  rw [Flapjack.WordToStackProofs.alistInsertGetVars moves source values
    ((parmove moves).map Prod.fst) distinct reads (allDistinctParmove moves distinct) wf
    (fun q member => memMapFstParmove moves q member)
    (fun q r member => parmovePreservesMoves moves q r ⟨distinct,member.1,member.2⟩)]

end Flapjack.WordToStackProofs.CompCorrect.Move
