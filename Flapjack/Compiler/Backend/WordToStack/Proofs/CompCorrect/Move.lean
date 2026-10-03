import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.MoveAuxSimulation
import Flapjack.Compiler.Backend.WordToStack.Proofs.MoveDiv2
import Flapjack.Compiler.Backend.WordToStack.Proofs.MoveReconstruction
import Flapjack.Compiler.Backend.Parmove.Correct
import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Parmove
import Flapjack.Compiler.Backend.Parmove.AllDistinct.Parmove
import Flapjack.Compiler.Backend.Parmove.SourceMembershipWrapper
import Flapjack.Compiler.Backend.Parmove.PreservesMoves.Parmove

namespace Flapjack.WordToStackProofs.CompCorrect.Move
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.Parmove
open Flapjack.Compiler.Backend.WordToStackRegFormat

/-- Flapjack factoring of the original Move source nonerror branch. The
actual source evaluation derives distinct destinations, successful reads and
the complete source post-state; no scheduling or target result is assumed. -/
theorem sourceSuccess {width : Nat} [NeZero width] {C F : Type}
    (priority : Nat) (moves : List (Nat × Nat))
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate (.move priority moves) source = (result,post))
    (notError : result ≠ some .error) :
    ∃ values, (moves.map Prod.fst).Nodup ∧
      WordSemStateFiniteExact.getVars (moves.map Prod.snd) source=some values ∧
      result=none ∧ post=WordSemStateFiniteExact.setVars (moves.map Prod.fst) values source := by
  by_cases distinct : (moves.map Prod.fst).Nodup
  · cases reads : WordSemStateFiniteExact.getVars (moves.map Prod.snd) source with
    | none =>
      simp [WordSemStateFiniteExact.evaluate,distinct,reads] at execution
      obtain ⟨rfl,rfl⟩ := execution
      contradiction
    | some values =>
      simp [WordSemStateFiniteExact.evaluate,distinct,reads] at execution
      obtain ⟨rfl,rfl⟩ := execution
      exact ⟨values,distinct,rfl,rfl,rfl⟩
  · simp [WordSemStateFiniteExact.evaluate,distinct] at execution
    obtain ⟨rfl,rfl⟩ := execution
    contradiction

/-- Flapjack original Move inline halving argument: even distinct source
 destinations give distinct halved destinations for the actual scheduler. -/
theorem halvedWindmill (moves : List (Nat × Nat))
    (distinct : (moves.map Prod.fst).Nodup)
    (even : ∀ n ∈ moves.map Prod.fst, n % 2=0) :
    windmill (moves.map (Prod.map (· /2) (· /2))) := by
  have halfDistinct := distinct.map_on (f := fun n : Nat => n/2) (by
    intro x hx y hy same
    have ex := even x hx
    have ey := even y hy
    omega)
  simpa [windmill,List.map_map,Function.comp_def] using halfDistinct

/-- Flapjack original scratch guard discharge: the scheduler proves that every
scratch read follows its first assignment, independently of its initial value. -/
theorem scheduledScratchReady {β : Type} (moves : List (Nat × Nat))
    (env : Option Nat → Option β) (valid : windmill moves) :
    MoveAuxStep.ScratchReady (parmove moves) env := by
  have safe := parmoveNotUseTempBeforeAssign moves valid
  unfold MoveAuxStep.ScratchReady
  cases read : Flapjack.Misc.findIndex none ((parmove moves).map Prod.snd) 0 with
  | none => trivial
  | some i =>
    cases write : Flapjack.Misc.findIndex none ((parmove moves).map Prod.fst) 0 with
    | none => simp [read,write] at safe
    | some j =>
      have earlier : ¬ i≤j := by simpa [read,write] using safe
      intro impossible
      exact False.elim (earlier impossible)

/-- Flapjack original real scheduled read success, derived from literal source
membership, even source variables and the original successful source getVars. -/
theorem scheduledReads {width : Nat} [NeZero width] {C F : Type}
    (moves : List (Nat × Nat)) (source : WordSemStateFiniteExact width C F)
    (even : ∀ n ∈ moves.map Prod.snd, n % 2=0)
    (reads : (WordSemStateFiniteExact.getVars (moves.map Prod.snd) source).isSome=true) :
    (WordSemStateFiniteExact.getVars
      (MoveAuxStep.realSources (parmove (moves.map (Prod.map (· /2) (· /2))))) source).isSome=true := by
  apply (NativeWordAccessors.isSomeGetVarsEvery _ source).mpr
  intro n member
  simp only [MoveAuxStep.realSources] at member
  obtain ⟨optional,filtered,projection⟩ := List.mem_map.mp member
  obtain ⟨scheduled,present⟩ := List.mem_filter.mp filtered
  subst n
  cases optional with
  | none => simp at present
  | some i =>
    have original := memMapSndParmove (moves.map (Prod.map (· /2) (· /2))) i scheduled
    simp only [List.map_map,Function.comp_def,Prod.map_snd,List.mem_map] at original
    obtain ⟨⟨dst,src⟩,input,eq⟩ := original
    have parity := even src (List.mem_map.mpr ⟨(dst,src),input,rfl⟩)
    have same : 2*i=src := by dsimp at eq; omega
    simp only [Option.getD_some,same]
    exact (NativeWordAccessors.isSomeGetVarsEvery _ source).mp reads src
      (List.mem_map.mpr ⟨(dst,src),input,rfl⟩)

/-- Flapjack original frame guard discharge from literal scheduler endpoint
membership and the original source maximum-variable bound. -/
theorem scheduledBounds (moves : List (Nat × Nat)) (frame k : Nat)
    (bound : maxList (moves.map Prod.fst ++ moves.map Prod.snd)<2*frame+2*k) :
    ∀ x y, (x,y) ∈ parmove (moves.map (Prod.map (· /2) (· /2))) →
      ∀ a, x=some a ∨ y=some a → a<frame+k := by
  intro x y member a occurs
  rcases occurs with rfl | rfl
  · have original := memMapFstParmove (moves.map (Prod.map (· /2) (· /2))) a
      (List.mem_map.mpr ⟨(some a,y),member,rfl⟩)
    simp only [List.map_map,Function.comp_def,Prod.map_fst,List.mem_map] at original
    obtain ⟨⟨dst,src⟩,input,half⟩ := original
    have upper := maxList_ge_of_mem (moves.map Prod.fst ++ moves.map Prod.snd) dst
      (List.mem_append_left _ (List.mem_map.mpr ⟨(dst,src),input,rfl⟩))
    dsimp at half
    omega
  · have original := memMapSndParmove (moves.map (Prod.map (· /2) (· /2))) a
      (List.mem_map.mpr ⟨(x,some a),member,rfl⟩)
    simp only [List.map_map,Function.comp_def,Prod.map_snd,List.mem_map] at original
    obtain ⟨⟨dst,src⟩,input,half⟩ := original
    have upper := maxList_ge_of_mem (moves.map Prod.fst ++ moves.map Prod.snd) src
      (List.mem_append_right _ (List.mem_map.mpr ⟨(dst,src),input,rfl⟩))
    dsimp at half
    omega

/-- Flapjack original Move environment, using actual source reads and the
actual target scratch value. No independently assumed environment relation. -/
def moveEnv {width : Nat} [NeZero width] {C F : Type} (k : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) : Option Nat → Option (WordLocW width)
  | none => StackSemStateOps.getVar (k+1) target
  | some i => WordSemStateFiniteExact.getVar (2*i) source

/-- Flapjack inline full native scheduled execution from original source-side
Move guards. The actual target run, scheduled source state relation and both
stack resource equalities are derived, with no desired result assumption. -/
theorem actualScheduledRun {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (lens : List Nat)
    (moves : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (related : stateRel ac k f frame source target lens 0)
    (distinct : (moves.map Prod.fst).Nodup)
    (evenDest : ∀ n ∈ moves.map Prod.fst, n % 2=0)
    (evenSrc : ∀ n ∈ moves.map Prod.snd, n % 2=0)
    (reads : (WordSemStateFiniteExact.getVars (moves.map Prod.snd) source).isSome=true)
    (bound : maxList (moves.map Prod.fst ++ moves.map Prod.snd)<2*frame+2*k) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wMoveNative moves (k,f,frame),target)=(none,post) ∧
      stateRel ac k f frame
        (MoveAuxReconstruction.sourcePost
          (parmove (moves.map (Prod.map (· /2) (· /2)))) (moveEnv k source target) source)
        post lens 0 ∧ post.stack.length=target.stack.length ∧ post.stackSpace=target.stackSpace := by
  have valid := halvedWindmill moves distinct evenDest
  have guards : MoveAuxSimulation.OriginalGuards ac k f frame lens
      (parmove (moves.map (Prod.map (· /2) (· /2)))) source target (moveEnv k source target) := by
    refine ⟨related,?_,?_,scheduledReads moves source evenSrc reads,
      scheduledScratchReady _ _ valid,scheduledBounds moves frame k bound,
      allDistinctParmove _ valid⟩
    · intro i value; rfl
    · intro value read; exact read
  obtain ⟨post,run,relation,length,space⟩ :=
    MoveAuxSimulation.evaluateWMoveAuxSeqsem ac k f frame lens _ source target _ guards
  refine ⟨post,?_,relation,length,space⟩
  have formatMap : Prod.map (formatVar k) (formatVar k) =
      (fun move : Option Nat × Option Nat => (formatVar k move.1,formatVar k move.2)) := by
    funext move; rcases move with ⟨x,y⟩; rfl
  have halfMap : Prod.map (fun n : Nat => n/2) (fun n : Nat => n/2) =
      (fun move : Nat × Nat => (move.1/2,move.2/2)) := by
    funext move; rcases move with ⟨x,y⟩; rfl
  simpa only [wMoveNative,formatMap,halfMap] using run

end Flapjack.WordToStackProofs.CompCorrect.Move
