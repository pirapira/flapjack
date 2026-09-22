import Flapjack.Crepe
import Flapjack.CrepeAssignedFreeVarsBound

/-!
# Original-domain parity for `crepLang$assigned_free_vars`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_assigned_free_vars_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:149-162`.
-/

namespace Flapjack.Test.CrepAssignedFreeVarsParity

open Flapjack

def parityGuard : Bool :=
  crepAssignedFreeVars (.skip : CrepProg Nat) == [] &&
  crepAssignedFreeVars (.assign 7 (.const 3) : CrepProg Nat) == [7] &&
  crepAssignedFreeVars
      (.dec 2 (.const 3)
        (.seq (.assign 2 (.const 4)) (.assign 5 (.const 6))) : CrepProg Nat) == [5] &&
  crepAssignedFreeVars
      (.seq (.assign 1 (.const 3)) (.assign 4 (.const 6)) : CrepProg Nat) == [1, 4] &&
  crepAssignedFreeVars
      (.ite (.const 1) (.assign 1 (.const 3)) (.assign 4 (.const 6)) : CrepProg Nat) == [1, 4] &&
  crepAssignedFreeVars
      (.while (.const 1) (.assign 6 (.const 8)) : CrepProg Nat) == [6] &&
  crepAssignedFreeVars
      (.shMem .load 9 (.const 0) : CrepProg Nat) == [9] &&
  crepAssignedFreeVars
      (.store (.const 0) (.const 1) : CrepProg Nat) == []

#eval parityGuard
#guard parityGuard

def boundedContext : CompileContext Nat :=
  { vars := [("fresh", (.one, [3]))], functions := [], exceptions := [],
    maxVar := 3, bytesInWord := 1 }

def raiseContext : CompileContext Nat :=
  { boundedContext with exceptions := [("error", 11)] }

/-! This fixture exercises the Cake `ctxt_max_el_leq` bridge on the same
    context-slot representation used by the assigned-free-vars proof. -/
theorem context_slot_bound_fixture :
    CrepContextSlot boundedContext 3 → 3 ≤ boundedContext.maxVar := by
  intro hslot
  apply crepContextSlot_le_max boundedContext ?_ hslot
  refine ⟨by omega, ?_⟩
  intro name shape slots hlookup
  simp [boundedContext, lookupInfo] at hlookup
  rcases hlookup with ⟨_hname, hshape, hslots⟩
  subst shape
  subst slots
  intro slot hmem
  simp [boundedContext] at *
  omega

theorem compileProg_dec_assigned_free_fixture :
    (7 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext (.dec "fresh" .one (.const 1) .skip)) := by
  apply not_mem_crepAssignedFreeVars_compileProg_dec
    boundedContext "fresh" .one (.const 1) .skip 7 [.const 1] .one
  · simp [compileExp]
  · simp [compileProg, crepAssignedFreeVars]

theorem compileProg_decCall_assigned_free_fixture :
    (7 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext
        (.decCall "fresh" .one "callee" [] .skip)) := by
  apply not_mem_crepAssignedFreeVars_compileProg_decCall
    boundedContext "fresh" .one "callee" [] .skip 7
  · simp [compileProg, crepAssignedFreeVars]
  · simp [allocatedNames, boundedContext]

theorem compileProg_primitive_assigned_free_fixture :
    (7 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext (.primitive "fresh" .addCarry [])) := by
  apply not_mem_crepAssignedFreeVars_compileProg_primitive
    boundedContext "fresh" .addCarry [] 7
  intro shape slots hlookup
  simp [boundedContext, lookupInfo] at hlookup
  rcases hlookup with ⟨rfl, rfl⟩
  simp

theorem compileProg_store_assigned_free_fixture :
    (9 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext (.store (.const 0) (.const 1))) := by
  exact not_mem_crepAssignedFreeVars_compileProg_store
    boundedContext (.const 0) (.const 1) 9

theorem compileProg_assign_local_direct_assigned_free_fixture :
    (7 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext
        (.assign .local "fresh" (.const 1))) := by
  apply not_mem_crepAssignedFreeVars_compileProg_assign_local
    boundedContext "fresh" (.const 1) 7
  intro shape slots hlookup
  simp [boundedContext, lookupInfo] at hlookup
  rcases hlookup with ⟨rfl, rfl⟩
  simp

theorem compileProg_assign_local_temporary_assigned_free_fixture :
    (7 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext
        (.assign .local "fresh" (.var .local "fresh"))) := by
  apply not_mem_crepAssignedFreeVars_compileProg_assign_local
    boundedContext "fresh" (.var .local "fresh") 7
  intro shape slots hlookup
  simp [boundedContext, lookupInfo] at hlookup
  rcases hlookup with ⟨rfl, rfl⟩
  simp

theorem compileProg_extCall_assigned_free_fixture :
    (9 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext
        (.extCall "ffi" (.const 1) (.const 2) (.const 3) (.const 4))) := by
  exact not_mem_crepAssignedFreeVars_compileProg_extCall
    boundedContext "ffi" (.const 1) (.const 2) (.const 3) (.const 4) 9

theorem compileProg_raise_assigned_free_fixture :
    (9 : Nat) ∉ crepAssignedFreeVars
      (compileProg raiseContext (.raise "error" (.const 1))) := by
  exact not_mem_crepAssignedFreeVars_compileProg_raise
    raiseContext "error" (.const 1) 9

theorem compileProg_shMemStore_assigned_free_fixture :
    (9 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext
        (.shMemStore .opW (.const 0) (.const 1))) := by
  exact not_mem_crepAssignedFreeVars_compileProg_shMemStore
    boundedContext .opW (.const 0) (.const 1) 9

theorem compileProg_store32_assigned_free_fixture :
    (9 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext (.store32 (.const 0) (.const 1))) := by
  exact not_mem_crepAssignedFreeVars_compileProg_store32
    boundedContext (.const 0) (.const 1) 9

theorem compileProg_storeByte_assigned_free_fixture :
    (9 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext (.storeByte (.const 0) (.const 1))) := by
  exact not_mem_crepAssignedFreeVars_compileProg_storeByte
    boundedContext (.const 0) (.const 1) 9

theorem compileProg_shMemLoad_local_assigned_free_fixture :
    (7 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext
        (.shMemLoad .opW .local "fresh" (.const 0))) := by
  apply not_mem_crepAssignedFreeVars_compileProg_shMemLoad_local
    boundedContext .opW "fresh" (.const 0) 7
  intro shape slots hlookup
  simp [boundedContext, lookupInfo] at hlookup
  rcases hlookup with ⟨rfl, rfl⟩
  simp

theorem compileProg_structural_composition_assigned_free_fixture :
    (7 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext
        (.seq .skip (.ite (.const 1) .skip (.while (.const 1) .skip)))) := by
  apply not_mem_crepAssignedFreeVars_compileProg_seq
    boundedContext .skip (.ite (.const 1) .skip (.while (.const 1) .skip)) 7
  · simp [compileProg, crepAssignedFreeVars]
  · apply not_mem_crepAssignedFreeVars_compileProg_ite
      boundedContext (.const 1) .skip (.while (.const 1) .skip) 7
    · simp [compileProg, crepAssignedFreeVars]
    · apply not_mem_crepAssignedFreeVars_compileProg_while
        boundedContext (.const 1) .skip 7
      simp [compileProg, crepAssignedFreeVars]

theorem compileProg_call_no_handler_assigned_free_fixture :
    (2 : Nat) ∉ crepAssignedFreeVars
      (compileProg boundedContext
        (.call (some (some (.local, "fresh"), none)) "callee" [])) := by
  apply not_mem_crepAssignedFreeVars_compileProg_call_no_handler
    boundedContext "callee" [] (some (.local, "fresh")) 2 (by simp [boundedContext])
  intro queriedName shape slots hlookup
  cases hname : ("fresh" == queriedName) with
  | false =>
      simp [boundedContext, lookupInfo] at hlookup
      rcases hlookup with ⟨hnameEq, hshapeEq, hslotsEq⟩
      subst queriedName
      simp at hname
  | true =>
      simp [boundedContext, lookupInfo] at hlookup
      rcases hlookup with ⟨hnameEq, hshapeEq, hslotsEq⟩
      rw [← hslotsEq]
      simp

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS crep assigned_free_vars skip/assign/dec/seq/if/while/shmem/fallback"
  else
    IO.println "FAIL crep assigned_free_vars parity"
  pure parityGuard

end Flapjack.Test.CrepAssignedFreeVarsParity
