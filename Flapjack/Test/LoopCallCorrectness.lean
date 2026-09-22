import Flapjack.LoopCallCorrectness

namespace Flapjack.Test.LoopCallCorrectness

open Flapjack
open Flapjack.LoopCall

def locValueState : LoopState Nat :=
  { locals := fun name => if name = 2 then some 7 else none
    globals := fun _ => none
    memory := fun _ => none }

theorem locValue_compile_correct_fixture :
    evalLoopProg 1 locValueState
        (comp [(1, 2)] (.locValue 3 2) : LoopProg Nat × LocationEnv).1 =
        some (.normal { locValueState with
          locals := updateLoopLocal locValueState.locals 3 7 }) ∧
      labelsIn (comp [(1, 2)] (.locValue 3 2) : LoopProg Nat × LocationEnv).2
        (updateLoopLocal locValueState.locals 3 7) := by
  apply comp_locValue_correct
  · simp [locValueState]
  · intro name source hlookup
    have hsource : source = 2 := by
      have hpair : 1 = name ∧ 2 = source := by
        simpa [lookup] using hlookup
      exact hpair.2.symm
    subst source
    exact ⟨7, by simp [locValueState]⟩

def load32State : LoopState Nat :=
  { locals := fun name => if name = 2 then some 100 else
      if name = 3 then some 7 else none
    globals := fun _ => none
    memory := fun address => if address = 100 then some 7 else none }

theorem load32_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.load32 2 3) : LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := updateLoopLocal load32State.locals 3 7 }) ∧
      labelsIn (comp [(3, 2)] (.load32 2 3) : LoopProg Nat × LocationEnv).2
        (updateLoopLocal load32State.locals 3 7) := by
  apply comp_load32_correct (addressValue := 100) (value := 7)
  · simp [load32State]
  · simp [load32State]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem loadByte_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.loadByte 2 3) : LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := updateLoopLocal load32State.locals 3 7 }) ∧
      labelsIn (comp [(3, 2)] (.loadByte 2 3) : LoopProg Nat × LocationEnv).2
        (updateLoopLocal load32State.locals 3 7) := by
  apply comp_loadByte_correct (addressValue := 100) (value := 7)
  · simp [load32State]
  · simp [load32State]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem store32_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.store32 2 3) : LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          memory := updateLoopMemory load32State.memory 100 7 }) ∧
      labelsIn (comp [(3, 2)] (.store32 2 3) : LoopProg Nat × LocationEnv).2
        ({ load32State with
          memory := updateLoopMemory load32State.memory 100 7 }).locals := by
  apply comp_store32_correct (addressValue := 100) (valueValue := 7)
  · simp [load32State]
  · simp [load32State]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem storeByte_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.storeByte 2 3) : LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          memory := updateLoopMemory load32State.memory 100 7 }) ∧
      labelsIn (comp [(3, 2)] (.storeByte 2 3) : LoopProg Nat × LocationEnv).2
        ({ load32State with
          memory := updateLoopMemory load32State.memory 100 7 }).locals := by
  apply comp_storeByte_correct (addressValue := 100) (valueValue := 7)
  · simp [load32State]
  · simp [load32State]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem store_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.store (.var 2) 3) : LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          memory := updateLoopMemory load32State.memory 100 7 }) ∧
      labelsIn (comp [(3, 2)] (.store (.var 2) 3) : LoopProg Nat × LocationEnv).2
        ({ load32State with
          memory := updateLoopMemory load32State.memory 100 7 }).locals := by
  apply comp_store_correct (addressValue := 100) (valueValue := 7)
  · simp [load32State, evalLoopExp]
  · simp [load32State]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem skip_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.skip : LoopProg Nat) : LoopProg Nat × LocationEnv).1 =
        some (.normal load32State) ∧
      labelsIn (comp [(3, 2)] (.skip : LoopProg Nat) : LoopProg Nat × LocationEnv).2
        load32State.locals := by
  apply comp_skip_correct
  intro name source hlookup
  have hpair : 3 = name ∧ 2 = source := by
    simpa [lookup] using hlookup
  have hsource : source = 2 := hpair.2.symm
  subst source
  exact ⟨100, by simp [load32State]⟩

theorem assign_var_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.assign 4 (.var 3)) : LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := updateLoopLocal load32State.locals 4 7 }) ∧
      labelsIn (comp [(3, 2)] (.assign 4 (.var 3)) : LoopProg Nat × LocationEnv).2
        (updateLoopLocal load32State.locals 4 7) := by
  apply comp_assign_var_correct
  · simp [load32State]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem assign_const_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.assign 4 (.const 11)) : LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := updateLoopLocal load32State.locals 4 11 }) ∧
      labelsIn (comp [(3, 2)] (.assign 4 (.const 11)) : LoopProg Nat × LocationEnv).2
        (updateLoopLocal load32State.locals 4 11) := by
  apply comp_assign_nonvar_correct
  · intro source
    simp
  · simp [evalLoopExp]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem tick_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.tick : LoopProg Nat)).1 =
        some (.normal load32State) ∧
      labelsIn (comp [(3, 2)] (.tick : LoopProg Nat)).2
        load32State.locals := by
  apply comp_tick_correct
  intro name source hlookup
  have hpair : 3 = name ∧ 2 = source := by
    simpa [lookup] using hlookup
  have hsource : source = 2 := hpair.2.symm
  subst source
  exact ⟨100, by simp [load32State]⟩

theorem setGlobal_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.setGlobal 9 (.const 11) : LoopProg Nat)).1 =
        some (.normal { load32State with
          globals := updateLoopGlobal load32State.globals 9 11 }) ∧
      labelsIn (comp [(3, 2)] (.setGlobal 9 (.const 11) : LoopProg Nat)).2
        ({ load32State with
          globals := updateLoopGlobal load32State.globals 9 11 }).locals := by
  apply comp_setGlobal_correct
  · simp [evalLoopExp]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem return_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.return [2, 3] : LoopProg Nat)).1 =
        some (.returned load32State [100, 7]) ∧
      labelsIn (comp [(3, 2)] (.return [2, 3] : LoopProg Nat)).2
        load32State.locals := by
  apply comp_return_correct
  · simp [loopReadLocals, load32State]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem raise_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.raise 2 : LoopProg Nat)).1 =
        some (.raised load32State 100) ∧
      labelsIn (comp [(3, 2)] (.raise 2 : LoopProg Nat)).2
        load32State.locals := by
  apply comp_raise_correct
  · simp [load32State]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem break_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.break 7 : LoopProg Nat)).1 =
        some (.broke load32State 7) ∧
      labelsIn (comp [(3, 2)] (.break 7 : LoopProg Nat)).2
        load32State.locals := by
  apply comp_break_correct
  intro name source hlookup
  have hpair : 3 = name ∧ 2 = source := by
    simpa [lookup] using hlookup
  have hsource : source = 2 := hpair.2.symm
  subst source
  exact ⟨100, by simp [load32State]⟩

theorem continue_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.continue 7 : LoopProg Nat)).1 =
        some (.continued load32State 7) ∧
      labelsIn (comp [(3, 2)] (.continue 7 : LoopProg Nat)).2
        load32State.locals := by
  apply comp_continue_correct
  intro name source hlookup
  have hpair : 3 = name ∧ 2 = source := by
    simpa [lookup] using hlookup
  have hsource : source = 2 := hpair.2.symm
  subst source
  exact ⟨100, by simp [load32State]⟩

theorem shMem_load_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.shMem .load 4 (.var 2)) : LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := updateLoopLocal load32State.locals 4 7 }) ∧
      labelsIn
        (comp [(3, 2)] (.shMem .load 4 (.var 2)) : LoopProg Nat × LocationEnv).2
        (updateLoopLocal load32State.locals 4 7) := by
  apply comp_shMem_load_correct (addressValue := 100) (value := 7)
  · exact Or.inl rfl
  · simp [evalLoopExp, load32State]
  · simp [load32State]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem shMem_store_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.shMem .store 3 (.var 2)) : LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          memory := updateLoopMemory load32State.memory 100 7 }) ∧
      labelsIn
        (comp [(3, 2)] (.shMem .store 3 (.var 2)) : LoopProg Nat × LocationEnv).2
        ({ load32State with
          memory := updateLoopMemory load32State.memory 100 7 }).locals := by
  apply comp_shMem_store_correct (addressValue := 100) (value := 7)
  · exact Or.inl rfl
  · simp [evalLoopExp, load32State]
  · simp [load32State]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem arith_div_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.arith (.div 4 3 2)) : LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := updateLoopLocal load32State.locals 4 (7 / 100) }) ∧
      labelsIn
        (comp [(3, 2)] (.arith (.div 4 3 2)) : LoopProg Nat × LocationEnv).2
        (updateLoopLocal load32State.locals 4 (7 / 100)) := by
  apply comp_arith_div_correct (destination := 4) (dividend := 3) (divisor := 2)
    (dividendValue := 7) (divisorValue := 100)
  · simp [load32State]
  · simp [load32State]
  · simp
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem primitive_labelsIn_fixture :
    (comp [(3, 2), (4, 3)] (.primitive [3] .addCarry [2, 3]) :
      LoopProg Nat × LocationEnv).1 = .primitive [3] .addCarry [2, 3] ∧
      labelsIn
        (comp [(3, 2), (4, 3)] (.primitive [3] .addCarry [2, 3] : LoopProg Nat)).2
        load32State.locals := by
  apply comp_primitive_labelsIn
  intro name source hlookup
  by_cases hname : name = 3
  · subst name
    have hsource : source = 2 := by
      have hpair : 1 = 1 ∧ 2 = source := by
        simpa [lookup] using hlookup
      exact hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩
  · have hname' : 3 ≠ name := Ne.symm hname
    by_cases hname4 : name = 4
    · subst name
      have hsource : source = 3 := by
        have hpair : 3 = 3 ∧ 3 = source := by
          simpa [lookup] using hlookup
        exact hpair.2.symm
      subst source
      exact ⟨7, by simp [load32State]⟩
    · have hnone : lookup name [(3, 2), (4, 3)] = none := by
        have hname4' : 4 ≠ name := Ne.symm hname4
        simp [lookup, hname', hname4']
      simp [hnone] at hlookup

#check comp_locValue_correct
#check comp_load32_correct
#check comp_loadByte_correct
#check comp_store32_correct
#check comp_storeByte_correct
#check comp_store_correct
#check comp_skip_correct
#check comp_assign_var_correct
#check comp_assign_nonvar_correct
#check comp_tick_correct
#check comp_setGlobal_correct
#check comp_return_correct
#check comp_raise_correct
#check comp_break_correct
#check comp_continue_correct
#check comp_shMem_load_correct
#check comp_shMem_store_correct
#check comp_arith_div_correct
#check comp_primitive_labelsIn

end Flapjack.Test.LoopCallCorrectness
