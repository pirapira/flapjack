import Flapjack.LoopCallCorrectness
import Flapjack.RiscV.Model

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

theorem fail_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.fail : LoopProg Nat)).1 = none ∧
      labelsIn (comp [(3, 2)] (.fail : LoopProg Nat)).2
        load32State.locals := by
  apply comp_fail_correct
  intro name source hlookup
  have hpair : 3 = name ∧ 2 = source := by
    simpa [lookup] using hlookup
  have hsource : source = 2 := hpair.2.symm
  subst source
  exact ⟨100, by simp [load32State]⟩

theorem mark_labelsIn_fixture :
    (comp [(3, 2)] (.mark (.fail : LoopProg Nat)) : LoopProg Nat × LocationEnv).1 =
        .mark (.fail : LoopProg Nat) ∧
      labelsIn
        (comp [(3, 2)] (.mark (.fail : LoopProg Nat))).2
        load32State.locals := by
  have henvironment : labelsIn [(3, 2)] load32State.locals := by
    intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩
  have hmarked := comp_mark_labelsIn
    (environment := [(3, 2)]) (body := (.fail : LoopProg Nat))
    (locals := load32State.locals) (by simpa [comp] using henvironment)
  simpa [comp] using hmarked

theorem mark_compile_correct_fixture :
    evalLoopProg 2 load32State
        (comp [(3, 2)] (.mark (.tick : LoopProg Nat)) :
          LoopProg Nat × LocationEnv).1 =
        some (.normal load32State) ∧
      labelsIn
        (comp [(3, 2)] (.mark (.tick : LoopProg Nat)) :
          LoopProg Nat × LocationEnv).2
        (loopResultState (.normal load32State)).locals := by
  have hmark := comp_mark_correct
    (environment := [(3, 2)]) (state := load32State) (fuel := 1)
    (body := (.tick : LoopProg Nat)) (result := .normal load32State)
    (by simp [comp, evalLoopProg]) (by simp [comp, labelsIn, lookup])
  simpa [comp, loopResultState] using hmark

theorem seq_labelsIn_fixture :
    (comp [(3, 2)]
      (.seq (.fail : LoopProg Nat) .tick) : LoopProg Nat × LocationEnv).1 =
        .seq .fail .tick ∧
      labelsIn
        (comp [(3, 2)]
          (.seq (.fail : LoopProg Nat) .tick)).2
        load32State.locals := by
  have hseq := comp_seq_labelsIn
    (environment := [(3, 2)]) (first := (.fail : LoopProg Nat))
    (second := .tick) (locals := load32State.locals)
  simpa [comp] using hseq

theorem seq_normal_compile_correct_fixture :
    evalLoopProg 2 load32State
        (comp [(3, 2)]
          (.seq (.tick : LoopProg Nat) .tick)).1 =
        some (.normal load32State) ∧
      labelsIn
        (comp [(3, 2)]
          (.seq (.tick : LoopProg Nat) .tick)).2
        (loopResultState (.normal load32State)).locals := by
  have hseq := comp_seq_normal_correct
    (environment := [(3, 2)]) (state := load32State) (fuel := 1)
    (first := (.tick : LoopProg Nat)) (second := .tick)
    (middle := load32State) (result := .normal load32State)
    (by simp [comp, evalLoopProg]) (by simp [comp, evalLoopProg])
  simpa [comp, loopResultState] using hseq

theorem seq_returned_compile_correct_fixture :
    evalLoopProg 2 load32State
        (comp [(3, 2)]
          (.seq (.return [] : LoopProg Nat) .tick)).1 =
        some (.returned load32State []) ∧
      labelsIn
        (comp [(3, 2)]
          (.seq (.return [] : LoopProg Nat) .tick)).2
        load32State.locals := by
  have hseq := comp_seq_returned_correct
    (environment := [(3, 2)]) (state := load32State) (fuel := 1)
    (first := (.return [] : LoopProg Nat)) (second := .tick)
    (middle := load32State) (values := [])
    (by simp [comp, evalLoopProg, loopReadLocals])
  simpa [comp] using hseq

theorem seq_broke_compile_correct_fixture :
    evalLoopProg 2 load32State
        (comp [(3, 2)]
          (.seq (.break 7 : LoopProg Nat) .tick)).1 =
        some (.broke load32State 7) ∧
      labelsIn
        (comp [(3, 2)]
          (.seq (.break 7 : LoopProg Nat) .tick)).2
        load32State.locals := by
  have hseq := comp_seq_broke_correct
    (environment := [(3, 2)]) (state := load32State) (fuel := 1)
    (first := (.break 7 : LoopProg Nat)) (second := .tick)
    (middle := load32State) (label := 7)
    (by simp [comp, evalLoopProg])
  simpa [comp] using hseq

theorem seq_continued_compile_correct_fixture :
    evalLoopProg 2 load32State
        (comp [(3, 2)]
          (.seq (.continue 7 : LoopProg Nat) .tick)).1 =
        some (.continued load32State 7) ∧
      labelsIn
        (comp [(3, 2)]
          (.seq (.continue 7 : LoopProg Nat) .tick)).2
        load32State.locals := by
  have hseq := comp_seq_continued_correct
    (environment := [(3, 2)]) (state := load32State) (fuel := 1)
    (first := (.continue 7 : LoopProg Nat)) (second := .tick)
    (middle := load32State) (label := 7)
    (by simp [comp, evalLoopProg])
  simpa [comp] using hseq

theorem seq_raised_compile_correct_fixture :
    evalLoopProg 2 load32State
        (comp [(3, 2)]
          (.seq (.raise 2 : LoopProg Nat) .tick)).1 =
        some (.raised load32State 100) ∧
      labelsIn
        (comp [(3, 2)]
          (.seq (.raise 2 : LoopProg Nat) .tick)).2
        load32State.locals := by
  have hseq := comp_seq_raised_correct
    (environment := [(3, 2)]) (state := load32State) (fuel := 1)
    (first := (.raise 2 : LoopProg Nat)) (second := .tick)
    (middle := load32State) (exception := 100)
    (by simp [comp, evalLoopProg, load32State])
  simpa [comp] using hseq

theorem ite_labelsIn_fixture :
    (comp [(3, 2)]
      (.ite .equal 2 (.imm 7) (.fail : LoopProg Nat) .tick [2]) :
        LoopProg Nat × LocationEnv).1 =
        .ite .equal 2 (.imm 7) .fail .tick [2] ∧
      labelsIn
        (comp [(3, 2)]
          (.ite .equal 2 (.imm 7) (.fail : LoopProg Nat) .tick [2])).2
        load32State.locals := by
  have hite := comp_ite_labelsIn
    (environment := [(3, 2)]) (operator := .equal) (condition := 2)
    (right := .imm 7) (thenBranch := (.fail : LoopProg Nat))
    (elseBranch := .tick) (live := [2]) (locals := load32State.locals)
  simpa [comp] using hite

theorem ite_true_compile_correct_fixture :
    evalLoopProg 2 load32State
        (comp [(3, 2)]
          (.ite .notEqual 2 (.imm 7) (.tick : LoopProg Nat) .fail [2])).1 =
        some (.normal load32State) ∧
      labelsIn
        (comp [(3, 2)]
          (.ite .notEqual 2 (.imm 7) (.tick : LoopProg Nat) .fail [2])).2
        (loopResultState (.normal load32State)).locals := by
  have hite := comp_ite_true_correct
    (environment := [(3, 2)]) (state := load32State) (fuel := 1)
    (operator := .notEqual) (condition := 2) (right := .imm 7)
    (thenBranch := (.tick : LoopProg Nat)) (elseBranch := .fail)
    (live := [2]) (leftValue := 100) (rightValue := 7)
    (result := .normal load32State)
    (by simp [load32State]) (by simp)
    (by simp [evalLoopCondition]) (by simp [comp, evalLoopProg])
  simpa [comp, loopResultState] using hite

theorem ite_false_compile_correct_fixture :
    evalLoopProg 2 load32State
        (comp [(3, 2)]
          (.ite .equal 2 (.imm 7) (.fail : LoopProg Nat) .tick [2])).1 =
        some (.normal load32State) ∧
      labelsIn
        (comp [(3, 2)]
          (.ite .equal 2 (.imm 7) (.fail : LoopProg Nat) .tick [2])).2
        (loopResultState (.normal load32State)).locals := by
  have hite := comp_ite_false_correct
    (environment := [(3, 2)]) (state := load32State) (fuel := 1)
    (operator := .equal) (condition := 2) (right := .imm 7)
    (thenBranch := (.fail : LoopProg Nat)) (elseBranch := .tick)
    (live := [2]) (leftValue := 100) (rightValue := 7)
    (result := .normal load32State)
    (by simp [load32State]) (by simp)
    (by simp [evalLoopCondition]) (by simp [comp, evalLoopProg])
  simpa [comp, loopResultState] using hite

theorem loop_labelsIn_fixture :
    (comp [(3, 2)]
      (.loop [2] (.fail : LoopProg Nat) [3]) : LoopProg Nat × LocationEnv).1 =
        .loop [2] .fail [3] ∧
      labelsIn
        (comp [(3, 2)]
          (.loop [2] (.fail : LoopProg Nat) [3])).2
        load32State.locals := by
  have hloop := comp_loop_labelsIn
    (environment := [(3, 2)]) (liveIn := [2]) (body := (.fail : LoopProg Nat))
    (liveOut := [3]) (locals := load32State.locals)
  simpa [comp, loopResultState] using hloop

theorem loop_repeat_compile_correct_fixture :
    evalLoopProg 3 load32State
        (comp [(3, 2)]
          (.loop [2] (.break 0 : LoopProg Nat) [3])).1 =
        some (.normal load32State) ∧
      labelsIn
        (comp [(3, 2)]
          (.loop [2] (.break 0 : LoopProg Nat) [3])).2
        load32State.locals := by
  have hloop := comp_loop_repeat_correct
    (environment := [(3, 2)]) (state := load32State) (fuel := 2)
    (liveIn := [2]) (body := (.break 0 : LoopProg Nat)) (liveOut := [3])
    (result := .normal load32State)
    (by simp [comp, evalLoopRepeat, evalLoopProg])
  simpa [comp, loopResultState] using hloop

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

theorem arith_longMul_compile_correct_fixture :
    evalLoopProg 1 load32State
        (comp [(3, 2)] (.arith (.longMul 4 4 3 2)) : LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := updateLoopLocal load32State.locals 4 (7 * 100) }) ∧
      labelsIn
        (comp [(3, 2)] (.arith (.longMul 4 4 3 2)) : LoopProg Nat × LocationEnv).2
        (updateLoopLocal load32State.locals 4 (7 * 100)) := by
  apply comp_arith_longMul_correct (destinationLeft := 4) (destinationRight := 4)
    (sourceLeft := 3) (sourceRight := 2) (leftValue := 7) (rightValue := 100)
  · rfl
  · simp [load32State]
  · simp [load32State]
  · intro name source hlookup
    have hpair : 3 = name ∧ 2 = source := by
      simpa [lookup] using hlookup
    have hsource : source = 2 := hpair.2.symm
    subst source
    exact ⟨100, by simp [load32State]⟩

theorem arith_longDiv_labelsIn_fixture :
    (comp [(3, 2)] (.arith (.longDiv 4 4 3 2 5)) : LoopProg Nat × LocationEnv).1 =
        .arith (.longDiv 4 4 3 2 5) ∧
      labelsIn
        (comp [(3, 2)] (.arith (.longDiv 4 4 3 2 5)) : LoopProg Nat × LocationEnv).2
        load32State.locals := by
  apply comp_arith_longDiv_labelsIn
  intro name source hlookup
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

def longDivWordState : LoopState (RiscV.Word 64) :=
  { locals := fun name => if name = 2 then some 100 else
      if name = 3 then some 7 else none
    globals := fun _ => none
    memory := fun _ => none }

theorem arith_longDiv_full_compile_correct_fixture :
    evalLoopProgFullWithLongDiv
        (fun high low divisor : RiscV.Word 64 => some (high + low, divisor)) 1
        longDivWordState
        (comp [(3, 2)]
          (.arith (.longDiv 4 5 3 2 2)) :
            LoopProg (RiscV.Word 64) × LocationEnv).1 =
        some (.normal { longDivWordState with
          locals := updateLoopLocal
            (updateLoopLocal longDivWordState.locals 5 100) 4 107 }) ∧
      labelsIn
        (comp [(3, 2)]
          (.arith (.longDiv 4 5 3 2 2)) :
            LoopProg (RiscV.Word 64) × LocationEnv).2
        (updateLoopLocal
          (updateLoopLocal longDivWordState.locals 5 100) 4 107) := by
  have hlong := comp_arith_longDiv_full_correct
    (longDiv := (fun high low divisor : RiscV.Word 64 => some (high + low, divisor)))
    (environment := [(3, 2)]) (state := longDivWordState) (fuel := 0)
    (destinationLeft := 4) (destinationRight := 5)
    (sourceLeft := 3) (sourceRight := 2) (quotient := 2)
    (highValue := 7) (lowValue := 100) (divisorValue := 100)
    (quotientValue := 107) (remainderValue := 100)
    (by simp [longDivWordState]) (by simp [longDivWordState])
    (by simp [longDivWordState])
    (by simp) (by
      intro name source hlookup
      have hpair : 3 = name ∧ 2 = source := by
        simpa [lookup] using hlookup
      have hsource : source = 2 := hpair.2.symm
      subst source
      exact ⟨100, by simp [longDivWordState]⟩)
  simpa using hlong

theorem arith_longMul_full_compile_correct_fixture :
    evalLoopProgFullWithLongMul
        (fun left right : RiscV.Word 64 => some (left + right, left * right)) 1
        longDivWordState
        (comp [(3, 2)]
          (.arith (.longMul 4 5 3 2)) :
            LoopProg (RiscV.Word 64) × LocationEnv).1 =
        some (.normal { longDivWordState with
          locals := updateLoopLocal
            (updateLoopLocal longDivWordState.locals 4 107) 5 700 }) ∧
      labelsIn
        (comp [(3, 2)]
          (.arith (.longMul 4 5 3 2)) :
            LoopProg (RiscV.Word 64) × LocationEnv).2
        (updateLoopLocal
          (updateLoopLocal longDivWordState.locals 4 107) 5 700) := by
  have hlong := comp_arith_longMul_full_correct
    (longMul := (fun left right : RiscV.Word 64 => some (left + right, left * right)))
    (environment := [(3, 2)]) (state := longDivWordState) (fuel := 0)
    (destinationLeft := 4) (destinationRight := 5)
    (sourceLeft := 3) (sourceRight := 2)
    (leftValue := 7) (rightValue := 100)
    (highValue := 107) (lowValue := 700)
    (by simp [longDivWordState]) (by simp [longDivWordState])
    (by simp) (by
      intro name source hlookup
      have hpair : 3 = name ∧ 2 = source := by
        simpa [lookup] using hlookup
      have hsource : source = 2 := hpair.2.symm
      subst source
      exact ⟨100, by simp [longDivWordState]⟩)
  simpa using hlong

theorem call_labelsIn_fixture :
    (comp [(3, 2)]
      (.call none none [2, 3] none : LoopProg Nat) : LoopProg Nat × LocationEnv).1 =
        .call none (some 2) [2] none ∧
      labelsIn
        (comp [(3, 2)]
          (.call none none [2, 3] none : LoopProg Nat)).2
        load32State.locals := by
  have hcompiled := comp_call_labelsIn (environment := [(3, 2)])
    (returns := none) (target := none) (arguments := [2, 3]) (handler := none)
    (locals := load32State.locals) (by
      intro name source hlookup
      have hpair : 3 = name ∧ 2 = source := by
        simpa [lookup] using hlookup
      have hsource : source = 2 := hpair.2.symm
      subst source
      exact ⟨100, by simp [load32State]⟩)
  simpa [comp, compCall, splitLast, lookup] using hcompiled

theorem call_target_compile_correct_fixture :
    evalLoopProgWithCallsAndFfi
        [(1, [3], (.return [3] : LoopProg Nat))]
        (fun _ _ _ _ _ _ => none) 3 load32State
        (comp [(3, 2)]
          (.call none (some 1) [3] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.returned load32State [7]) ∧
      labelsIn
        (comp [(3, 2)]
          (.call none (some 1) [3] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        load32State.locals := by
  have hcall := comp_call_target_correct
    (functions := [(1, [3], (.return [3] : LoopProg Nat))])
    (ffiHandler := (fun _ _ _ _ _ _ => none))
    (environment := [(3, 2)]) (state := load32State) (fuel := 2)
    (returns := none) (target := 1) (arguments := [3]) (handler := none)
    (result := .returned load32State [7])
    (by
      simp [evalLoopCallWithCallsAndFfi, evalLoopProgWithCallsAndFfi,
        lookupLoopFunction, loopReadLocals, evalLoopProg, loopBindParameters,
        loopLookupFirst, load32State])
  simpa [comp, loopResultState] using hcall

theorem call_empty_compile_correct_fixture :
    evalLoopProgWithCallsAndFfi []
        (fun _ _ _ _ _ _ => none) 1 load32State
        (comp [(3, 2)]
          (.call none none [] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.normal load32State) ∧
      labelsIn
        (comp [(3, 2)]
          (.call none none [] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        load32State.locals := by
  have hcall := comp_call_empty_correct
    (functions := [])
    (ffiHandler := (fun _ _ _ _ _ _ => none))
    (environment := [(3, 2)]) (state := load32State) (fuel := 0)
    (returns := none) (handler := none)
  simpa [comp] using hcall

theorem call_implicit_target_compile_correct_fixture :
    evalLoopProgWithCallsAndFfi
        [(2, [], (.return [] : LoopProg Nat))]
        (fun _ _ _ _ _ _ => none) 3 load32State
        (comp [(3, 2)]
          (.call none none [3] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.returned load32State []) ∧
      labelsIn
        (comp [(3, 2)]
          (.call none none [3] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        load32State.locals := by
  have hcall := comp_call_implicit_target_correct
    (functions := [(2, [], (.return [] : LoopProg Nat))])
    (ffiHandler := (fun _ _ _ _ _ _ => none))
    (environment := [(3, 2)]) (state := load32State) (fuel := 2)
    (returns := none) (arguments := [3]) (pre := [])
    (lastValue := 3) (destination := 2) (handler := none)
    (result := .returned load32State [])
    (by simp [splitLast]) (by simp [lookup])
    (by
      simp [evalLoopCallWithCallsAndFfi, evalLoopProgWithCallsAndFfi,
        lookupLoopFunction, loopReadLocals, evalLoopProg, loopBindParameters,
        loopLookupFirst, load32State])
  simpa [comp, loopResultState] using hcall

theorem call_target_return_compile_correct_fixture :
    evalLoopProgWithCallsAndFfi
        [(1, [3], (.return [3] : LoopProg Nat))]
        (fun _ _ _ _ _ _ => none) 3 load32State
        (comp [(3, 2)]
          (.call (some ([4], [])) (some 1) [3] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := loopLookupFirst load32State.locals ([4].zip [7]) }) ∧
      labelsIn
        (comp [(3, 2)]
          (.call (some ([4], [])) (some 1) [3] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        (loopLookupFirst load32State.locals ([4].zip [7])) := by
  have hcall := comp_call_target_return_correct
    (functions := [(1, [3], (.return [3] : LoopProg Nat))])
    (ffiHandler := (fun _ _ _ _ _ _ => none))
    (environment := [(3, 2)]) (state := load32State) (fuel := 2)
    (destinations := [4]) (live := []) (target := 1) (arguments := [3])
    (values := [7]) (handler := none)
    (by
      simp [evalLoopCallWithCallsAndFfi, evalLoopProgWithCallsAndFfi,
        lookupLoopFunction, loopReadLocals, evalLoopProg, loopBindParameters,
        loopLookupFirst, loopAssignValues, load32State])
  simpa [comp, loopResultState] using hcall

theorem call_target_return_no_handler_semantic_fixture :
    evalLoopCallWithCallsAndFfi
        [(1, [3], (.return [3] : LoopProg Nat))]
        (fun _ _ _ _ _ _ => none) 3 load32State none (some 1) [3] none =
      some (.returned load32State [7]) := by
  apply evalLoopCallWithCallsAndFfi_returned_no_handler
    (functions := [(1, [3], (.return [3] : LoopProg Nat))])
    (ffiHandler := (fun _ _ _ _ _ _ => none))
    (fuel := 2) (state := load32State) (target := 1)
    (arguments := [3]) (parameters := [3])
    (body := (.return [3] : LoopProg Nat)) (argumentValues := [7])
    (calleeLocals := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (calleeState := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (values := [7])
  · simp [lookupLoopFunction]
  · simp [loopReadLocals, load32State]
  · simp [loopBindParameters, loopLookupFirst]
  · simp [evalLoopProgWithCallsAndFfi, evalLoopProg, loopLookupFirst,
      loopReadLocals, load32State]

theorem call_target_return_handler_compile_correct_fixture :
    evalLoopProgWithCallsAndFfi
        [(1, [3], (.return [3] : LoopProg Nat))]
        (fun _ _ _ _ _ _ => none) 3 load32State
        (comp [(3, 2)]
          (.call (some ([4], [])) (some 1) [3]
            (some (5, (.raise 5 : LoopProg Nat), .skip, [])) : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := loopLookupFirst load32State.locals ([4].zip [7]) }) ∧
      labelsIn
        (comp [(3, 2)]
          (.call (some ([4], [])) (some 1) [3]
            (some (5, (.raise 5 : LoopProg Nat), .skip, [])) : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        (loopLookupFirst load32State.locals ([4].zip [7])) := by
  have hcall := comp_call_target_return_handler_correct
    (functions := [(1, [3], (.return [3] : LoopProg Nat))])
    (ffiHandler := (fun _ _ _ _ _ _ => none))
    (environment := [(3, 2)]) (state := load32State) (fuel := 1)
    (returns := ([4], [])) (target := 1) (arguments := [3]) (parameters := [3])
    (body := (.return [3] : LoopProg Nat)) (argumentValues := [7])
    (calleeLocals := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (calleeState := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (exceptionName := 5) (exceptionBody := .raise 5) (normalBody := .skip)
    (handlerLive := []) (values := [7])
    (assignedLocals := loopLookupFirst load32State.locals ([4].zip [7]))
    (handlerState := { load32State with
      locals := loopLookupFirst load32State.locals ([4].zip [7]) })
    (by simp [lookupLoopFunction])
    (by simp [loopReadLocals, load32State])
    (by simp [loopBindParameters, loopLookupFirst])
    (by simp [evalLoopProgWithCallsAndFfi, evalLoopProg, loopLookupFirst,
      loopReadLocals, load32State])
    (by simp [loopAssignValues, loopLookupFirst])
    (by simp [evalLoopProgWithCallsAndFfi, evalLoopProg, loopLookupFirst])
  simpa [comp, loopResultState] using hcall

theorem call_target_return_handler_result_compile_correct_fixture :
    evalLoopProgWithCallsAndFfi
        [(1, [3], (.return [3] : LoopProg Nat))]
        (fun _ _ _ _ _ _ => none) 3 load32State
        (comp [(3, 2)]
          (.call (some ([4], [])) (some 1) [3]
            (some (5, (.skip : LoopProg Nat), (.raise 4 : LoopProg Nat), [])) :
            LoopProg Nat) : LoopProg Nat × LocationEnv).1 =
        some (.raised { load32State with
          locals := loopLookupFirst load32State.locals ([4].zip [7]) } 7) ∧
      labelsIn
        (comp [(3, 2)]
          (.call (some ([4], [])) (some 1) [3]
            (some (5, (.skip : LoopProg Nat), (.raise 4 : LoopProg Nat), [])) :
            LoopProg Nat) : LoopProg Nat × LocationEnv).2
        (loopLookupFirst load32State.locals ([4].zip [7])) := by
  have hcall := comp_call_target_return_handler_result_correct
    (functions := [(1, [3], (.return [3] : LoopProg Nat))])
    (ffiHandler := (fun _ _ _ _ _ _ => none))
    (environment := [(3, 2)]) (state := load32State) (fuel := 1)
    (returns := ([4], [])) (target := 1) (arguments := [3]) (parameters := [3])
    (body := (.return [3] : LoopProg Nat)) (argumentValues := [7])
    (calleeLocals := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (calleeState := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (exceptionName := 5) (exceptionBody := .skip)
    (normalBody := .raise 4) (handlerLive := []) (values := [7])
    (assignedLocals := loopLookupFirst load32State.locals ([4].zip [7]))
    (handlerResult := .raised
      { load32State with locals := loopLookupFirst load32State.locals ([4].zip [7]) } 7)
    (by simp [lookupLoopFunction])
    (by simp [loopReadLocals, load32State])
    (by simp [loopBindParameters, loopLookupFirst])
    (by simp [evalLoopProgWithCallsAndFfi, evalLoopProg, loopLookupFirst,
      loopReadLocals, load32State])
    (by simp [loopAssignValues, loopLookupFirst])
    (by simp [evalLoopProgWithCallsAndFfi, evalLoopProg, loopLookupFirst])
  simpa [comp, loopResultState] using hcall

theorem call_target_raised_no_handler_compile_correct_fixture :
    evalLoopProgWithCallsAndFfi
        [(1, [3], (.raise 3 : LoopProg Nat))]
        (fun _ _ _ _ _ _ => none) 3 load32State
        (comp [(3, 2)]
          (.call none (some 1) [3] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.raised { load32State with
          locals := load32State.locals } 7) ∧
      labelsIn
        (comp [(3, 2)]
          (.call none (some 1) [3] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        load32State.locals := by
  have hcall := comp_call_target_raised_no_handler_correct
    (functions := [(1, [3], (.raise 3 : LoopProg Nat))])
    (ffiHandler := (fun _ _ _ _ _ _ => none))
    (environment := [(3, 2)]) (fuel := 1) (state := load32State)
    (returns := none) (target := 1) (arguments := [3]) (parameters := [3])
    (body := (.raise 3 : LoopProg Nat)) (argumentValues := [7])
    (calleeLocals := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (calleeState := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (exception := 7)
    (by simp [lookupLoopFunction])
    (by simp [loopReadLocals, load32State])
    (by simp [loopBindParameters, loopLookupFirst])
    (by simp [evalLoopProgWithCallsAndFfi, evalLoopProg, loopLookupFirst])
  simpa [comp, loopResultState] using hcall

theorem call_target_raised_handler_compile_correct_fixture :
    evalLoopProgWithCallsAndFfi
        [(1, [3], (.raise 3 : LoopProg Nat))]
        (fun _ _ _ _ _ _ => none) 3 load32State
        (comp [(3, 2)]
          (.call (some ([], [])) (some 1) [3]
            (some (5, (.skip : LoopProg Nat), .skip, [])) : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := updateLoopLocal load32State.locals 5 7 }) ∧
      labelsIn
        (comp [(3, 2)]
          (.call (some ([], [])) (some 1) [3]
            (some (5, (.skip : LoopProg Nat), .skip, [])) : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        (updateLoopLocal load32State.locals 5 7) := by
  have hcall := comp_call_target_raised_handler_correct
    (functions := [(1, [3], (.raise 3 : LoopProg Nat))])
    (ffiHandler := (fun _ _ _ _ _ _ => none))
    (environment := [(3, 2)]) (fuel := 1) (state := load32State)
    (returns := ([], [])) (target := 1) (arguments := [3]) (parameters := [3])
    (body := (.raise 3 : LoopProg Nat)) (argumentValues := [7])
    (calleeLocals := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (calleeState := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (exceptionName := 5) (exceptionBody := .skip) (normalBody := .skip)
    (handlerLive := []) (exception := 7)
    (handlerState := { load32State with
      locals := updateLoopLocal load32State.locals 5 7 })
    (by simp [lookupLoopFunction])
    (by simp [loopReadLocals, load32State])
    (by simp [loopBindParameters, loopLookupFirst])
    (by simp [evalLoopProgWithCallsAndFfi, evalLoopProg, loopLookupFirst])
    (by simp [evalLoopProgWithCallsAndFfi, evalLoopProg])
  simpa [comp, loopResultState] using hcall

theorem call_target_raised_handler_result_compile_correct_fixture :
    evalLoopProgWithCallsAndFfi
        [(1, [3], (.raise 3 : LoopProg Nat))]
        (fun _ _ _ _ _ _ => none) 3 load32State
        (comp [(3, 2)]
          (.call (some ([], [])) (some 1) [3]
            (some (5, (.raise 5 : LoopProg Nat), .skip, [])) : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.raised { load32State with locals := updateLoopLocal load32State.locals 5 7 } 7) ∧
      labelsIn
        (comp [(3, 2)]
          (.call (some ([], [])) (some 1) [3]
            (some (5, (.raise 5 : LoopProg Nat), .skip, [])) : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        (updateLoopLocal load32State.locals 5 7) := by
  have hcall := comp_call_target_raised_handler_result_correct
    (functions := [(1, [3], (.raise 3 : LoopProg Nat))])
    (ffiHandler := (fun _ _ _ _ _ _ => none))
    (environment := [(3, 2)]) (fuel := 1) (state := load32State)
    (returns := ([], [])) (target := 1) (arguments := [3]) (parameters := [3])
    (body := (.raise 3 : LoopProg Nat)) (argumentValues := [7])
    (calleeLocals := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (calleeState := { load32State with
      locals := loopLookupFirst (fun _ => none) ([3].zip [7]) })
    (exceptionName := 5) (exceptionBody := .raise 5) (normalBody := .skip)
    (handlerLive := []) (exception := 7)
    (handlerResult := .raised { load32State with locals := updateLoopLocal load32State.locals 5 7 } 7)
    (by simp [lookupLoopFunction])
    (by simp [loopReadLocals, load32State])
    (by simp [loopBindParameters, loopLookupFirst])
    (by simp [evalLoopProgWithCallsAndFfi, evalLoopProg, loopLookupFirst])
    (by simp [evalLoopProgWithCallsAndFfi, evalLoopProg, updateLoopLocal])
  simpa [comp, loopResultState] using hcall

theorem call_implicit_target_unresolved_compile_fixture :
    evalLoopProgWithCallsAndFfi []
        (fun _ _ _ _ _ _ => none) 3 load32State
        (comp [(3, 2)]
          (.call none none [4] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 = none ∧
      labelsIn
        (comp [(3, 2)]
          (.call none none [4] none : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        load32State.locals := by
  exact comp_call_implicit_target_unresolved_correct
    (functions := [])
    (ffiHandler := (fun _ _ _ _ _ _ => none))
    (environment := [(3, 2)]) (state := load32State) (fuel := 2)
    (returns := none) (arguments := [4]) (pre := [])
    (lastValue := 4) (handler := none)
    (by simp [splitLast]) (by simp [lookup])

theorem ffi_labelsIn_fixture :
    (comp [(3, 2)]
      (.ffi "print" 1 2 3 4 [2, 3] : LoopProg Nat) : LoopProg Nat × LocationEnv).1 =
        .ffi "print" 1 2 3 4 [2, 3] ∧
      labelsIn
        (comp [(3, 2)]
          (.ffi "print" 1 2 3 4 [2, 3] : LoopProg Nat)).2
        load32State.locals := by
  apply comp_ffi_labelsIn
  intro name source hlookup
  have hpair : 3 = name ∧ 2 = source := by
    simpa [lookup] using hlookup
  have hsource : source = 2 := hpair.2.symm
  subst source
  exact ⟨100, by simp [load32State]⟩

theorem primitive_single_compile_correct_fixture :
    evalLoopProgWithPrimitive
        (fun _ _ => some [107]) 1 load32State
        (comp [(3, 2)]
          (.primitive [4] .addCarry [3] : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := updateLoopLocal load32State.locals 4 107 }) ∧
      labelsIn
        (comp [(3, 2)]
          (.primitive [4] .addCarry [3] : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        (updateLoopLocal load32State.locals 4 107) := by
  have hprimitive := comp_primitive_single_correct
    (primitive := (fun _ _ => some [107]))
    (environment := [(3, 2)]) (state := load32State) (fuel := 0)
    (destination := 4) (operator := .addCarry) (arguments := [3])
    (argumentValues := [7]) (value := 107)
    (by simp [load32State, loopReadLocals]) (by simp)
    (by
      intro name source hlookup
      have hpair : 3 = name ∧ 2 = source := by
        simpa [lookup] using hlookup
      have hsource : source = 2 := hpair.2.symm
      subst source
      exact ⟨100, by simp [load32State]⟩)
  simpa [comp] using hprimitive

theorem primitive_general_compile_correct_fixture :
    evalLoopProgWithPrimitive
        (fun _ _ => some [107, 700]) 1 load32State
        (comp [(3, 2)]
          (.primitive [4, 5] .addCarry [3] : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.normal { load32State with
          locals := loopLookupFirst load32State.locals [(4, 107), (5, 700)] }) ∧
      labelsIn
        (comp [(3, 2)]
          (.primitive [4, 5] .addCarry [3] : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        (loopLookupFirst load32State.locals [(4, 107), (5, 700)]) := by
  have hprimitive := comp_primitive_general_correct
    (primitive := (fun _ _ => some [107, 700]))
    (environment := [(3, 2)]) (state := load32State) (fuel := 0)
    (destinations := [4, 5]) (operator := .addCarry) (arguments := [3])
    (argumentValues := [7]) (values := [107, 700])
    (by simp [load32State, loopReadLocals]) (by simp) (by simp)
    (by
      intro name source hlookup
      have hpair : 3 = name ∧ 2 = source := by
        simpa [lookup] using hlookup
      have hsource : source = 2 := hpair.2.symm
      subst source
      exact ⟨100, by simp [load32State]⟩)
  simpa [comp] using hprimitive

theorem ffi_compile_correct_fixture :
    evalLoopProgWithCallsAndFfi []
        (fun _ _ _ _ _ state => some state) 1 load32State
        (comp [(3, 2)]
          (.ffi "print" 2 2 2 2 [3] : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.normal load32State) ∧
      labelsIn
        (comp [(3, 2)]
          (.ffi "print" 2 2 2 2 [3] : LoopProg Nat) :
            LoopProg Nat × LocationEnv).2
        load32State.locals := by
  have hffi := comp_ffi_correct
    (functions := [])
    (ffiHandler := (fun _ _ _ _ _ state => some state))
    (environment := [(3, 2)]) (state := load32State) (fuel := 0)
    (function := "print") (configuration := 2)
    (configurationLength := 2) (array := 2) (arrayLength := 2)
    (live := [3]) (configurationValue := 100)
    (configurationLengthValue := 100) (arrayValue := 100)
    (arrayLengthValue := 100) (resultState := load32State)
    (by simp [load32State]) (by simp [load32State])
    (by simp [load32State]) (by simp [load32State]) (by simp)
  simpa [comp] using hffi

theorem loop_compile_result_fixture :
    evalLoopProg 3 load32State
        (comp [(3, 2)]
          (.loop [2] (.break 0) [2] : LoopProg Nat) :
            LoopProg Nat × LocationEnv).1 =
        some (.normal load32State) ∧
      labelsIn
        (comp [(3, 2)]
          (.loop [2] (.break 0) [2] : LoopProg Nat)).2
        load32State.locals := by
  have hresult :
      evalLoopRepeat 2 load32State
          (comp ([] : LocationEnv) (.break 0 : LoopProg Nat)).1 =
        some (.normal load32State) := by
    simp [comp, evalLoopRepeat, evalLoopProg]
  have hloop := comp_loop_correct
    (environment := [(3, 2)]) (state := load32State) (fuel := 2)
    (liveIn := [2]) (liveOut := [2]) (body := (.break 0 : LoopProg Nat))
    (result := .normal load32State) hresult
  constructor
  · simpa [comp] using hloop.1
  · simpa [comp, loopResultState] using hloop.2

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
#check comp_fail_correct
#check comp_mark_labelsIn
#check comp_mark_correct
#check comp_seq_labelsIn
#check comp_seq_normal_correct
#check comp_seq_returned_correct
#check comp_seq_broke_correct
#check comp_seq_continued_correct
#check comp_seq_raised_correct
#check comp_ite_labelsIn
#check comp_ite_true_correct
#check comp_ite_false_correct
#check comp_loop_labelsIn
#check comp_loop_correct
#check comp_loop_repeat_correct
#check comp_setGlobal_correct
#check comp_return_correct
#check comp_raise_correct
#check comp_break_correct
#check comp_continue_correct
#check comp_shMem_load_correct
#check comp_shMem_store_correct
#check comp_arith_div_correct
#check comp_arith_longMul_correct
#check comp_arith_longMul_full_correct
#check comp_arith_longDiv_labelsIn
#check comp_arith_longDiv_full_correct
#check comp_primitive_labelsIn
#check comp_primitive_single_correct
#check comp_primitive_general_correct
#check comp_call_labelsIn
#check comp_call_target_correct
#check comp_call_target_return_correct
#check comp_call_target_return_handler_correct
#check comp_call_target_return_handler_result_correct
#check evalLoopCallWithCallsAndFfi_returned_no_handler
#check comp_call_target_raised_no_handler_correct
#check comp_call_target_raised_handler_correct
#check comp_call_target_raised_handler_result_correct
#check comp_call_empty_correct
#check comp_call_implicit_target_correct
#check comp_call_implicit_target_unresolved_correct
#check comp_ffi_labelsIn
#check comp_ffi_correct

end Flapjack.Test.LoopCallCorrectness
