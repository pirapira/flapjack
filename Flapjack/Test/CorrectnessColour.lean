import Flapjack.RiscV.CorrectnessColour
import Flapjack.RiscV.CorrectnessParallelMove

/-! Regression tests for the executable colouring simulation theorem. -/

namespace Flapjack.RiscV

def testColour (name : Nat) : Nat :=
  if name = 1 then 2 else if name = 2 then 1 else name

theorem testColourValidFn : wordColourValid testColour := by
  intro name hname
  by_cases hone : name = 1
  · simp [testColour, hone]
  · by_cases htwo : name = 2
    · simp [testColour, htwo]
    · simpa [testColour, hone, htwo] using hname

theorem testColour_valid : wordColourValid testColour := testColourValidFn

theorem testColour_injective : Function.Injective testColour := by
  intro left right h
  by_cases hleftOne : left = 1 <;> by_cases hleftTwo : left = 2 <;>
    by_cases hrightOne : right = 1 <;> by_cases hrightTwo : right = 2 <;>
      simp [testColour, hleftOne, hleftTwo, hrightOne, hrightTwo] at h ⊢ <;>
        omega

theorem testColour_zero : testColour 0 = 0 := by
  simp [testColour]

theorem testColour_noScratch : ∀ name, name < 31 → testColour name ≠ 31 := by
  intro name hname
  by_cases hone : name = 1
  · simp [testColour, hone]
  · by_cases htwo : name = 2
    · simp [testColour, htwo]
    · have hnot : name ≠ 31 := by omega
      simpa [testColour, hone, htwo] using hnot

def testRelation [NeZero width] (source target : State width) : Prop :=
  WordColourStateRelation testColour source target

def testTargetState [NeZero width] (state : State width) : State width :=
  { state with registers := fun register =>
      if register = 1 then state.registers 2
      else if register = 2 then state.registers 1
      else state.registers register }

theorem testRelation_target [NeZero width] (state : State width) :
    testRelation state (testTargetState state) := by
  unfold testRelation
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  intro name hname
  intro hcolour
  by_cases hone : name = 1
  · subst name
    change state.registers 1 = state.registers 1
    rfl
  · by_cases htwo : name = 2
    · subst name
      change state.registers 2 = state.registers 2
      rfl
    · have hone' : (⟨name, hname⟩ : Fin 32) ≠ 1 := by
        intro h
        apply hone
        exact congrArg Fin.val h
      have htwo' : (⟨name, hname⟩ : Fin 32) ≠ 2 := by
        intro h
        apply htwo
        exact congrArg Fin.val h
      simp [readRegister, testTargetState, testColour, hone, htwo, hone', htwo']

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state (.move 1 [(3, 4), (5, 6)]) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour (.move 1 [(3, 4), (5, 6)])) = some target' ∧
      testRelation source' target' := by
  exact evalWordProg_moveTwo_applyColour testColour testColourValidFn
    testColour_injective testColour_zero state (testTargetState state)
    (testRelation_target state) 3 4 5 6
    (by omega) (by omega) (by omega) (by omega)
    (by decide) (by decide) (by decide) (by decide)
    (by simp [testColour]) (by simp [testColour])
    (by simp [testColour]) (by simp [testColour])
    (by decide) (by decide) (by decide) (by decide) (by decide)

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state (.move 1 [(3, 4), (5, 6)]) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour (.move 1 [(3, 4), (5, 6)])) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state)
  · exact testRelation_target state
  · exact .moveTwo 3 4 5 6
      (by omega) (by omega) (by omega) (by omega)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state (.move 1 [(3, 4), (5, 6)]) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour (.move 1 [(3, 4), (5, 6)])) = some target' ∧
      testRelation source' target' := by
  exact evalWordProg_moveAcyclic_applyColour testColour testColourValidFn
    testColour_injective testColour_zero state (testTargetState state)
    (testRelation_target state) [(3, 4), (5, 6)]
    (by decide) (by decide) (by decide) (by decide)

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state
          (.seq (.move 1 [(5, 2), (9, 3)]) (.assign 1 (.var 5))) =
        some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.seq (.move 1 [(5, 2), (9, 3)]) (.assign 1 (.var 5)))) =
        some target' ∧
      testRelation source' target' := by
  apply evalWordProg_acyclicEntry_seq_applyColour testColour
    testColourValidFn testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state) (testRelation_target state)
    [(5, 2), (9, 3)] (by decide) (by decide) (by decide)
  · exact .assign 1 5 (by omega) (by omega)

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state (.move 1 [(3, 4)]) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour (.move 1 [(3, 4)])) = some target' ∧
      testRelation source' target' := by
  exact evalWordProg_moveOne_applyColour testColour testColourValidFn
    testColour_injective testColour_zero state (testTargetState state)
    (testRelation_target state) 3 4 (by omega) (by omega) (by decide) (by decide)
    (by simp [testColour]) (by simp [testColour]) (by decide)

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state (.move 1 [(3, 4)]) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour (.move 1 [(3, 4)])) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state)
  · exact testRelation_target state
  · exact .moveOne 3 4 (by omega) (by omega) (by decide) (by decide) (by decide)

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state
          (.seq (.assign 1 (.var 2)) (.assign 2 (.var 1))) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.seq (.assign 1 (.var 2)) (.assign 2 (.var 1)))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state)
  · exact testRelation_target state
  · exact .seq (.assign 1 2 (by omega) (by omega))
      (.assign 2 1 (by omega) (by omega))

example [NeZero width] (state : State width) (value : Word width) :
    ∃ source' target',
      evalWordProg state
          (.seq (.assign 1 (.const value)) (.assign 2 (.var 1))) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.seq (.assign 1 (.const value)) (.assign 2 (.var 1)))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state)
  · exact testRelation_target state
  · exact .seq (.assignConst 1 value (by omega))
      (.assign 2 1 (by omega) (by omega))

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state
          (.assign 3 (.op .add [.var 1, .var 2])) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.assign 3 (.op .add [.var 1, .var 2]))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state)
  · exact testRelation_target state
  · exact .assignBinary .add 3 1 2 (by omega) (by omega) (by omega)

example [NeZero width] (state : State width) (value : Word width) :
    ∃ source' target',
      evalWordProg state
          (.assign 3 (.op .and [.var 1, .const value])) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.assign 3 (.op .and [.var 1, .const value]))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state)
  · exact testRelation_target state
  · exact .assignImmediate .and 3 1 value (by omega) (by omega)

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state
          (.assign 3 (.shift .asr (.var 1) (.var 2))) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.assign 3 (.shift .asr (.var 1) (.var 2)))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state)
  · exact testRelation_target state
  · exact .assignShift .asr 3 1 2 (by decide) (by omega) (by omega) (by omega)

example [NeZero width] (state : State width) (amount : Word width) :
    ∃ source' target',
      evalWordProg state
          (.assign 3 (.shift .lsr (.var 1) (.const amount))) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.assign 3 (.shift .lsr (.var 1) (.const amount)))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state)
  · exact testRelation_target state
  · exact .assignShiftImmediate .lsr 3 1 amount (by decide) (by omega) (by omega)

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state
          (.assign 3 (.shift .ror (.var 1) (.var 2))) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.assign 3 (.shift .ror (.var 1) (.var 2)))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_assignRotateRight_applyColour testColour
    testColourValidFn testColour_injective testColour_zero (by simp [testColour])
    state (testTargetState state)
  · exact testRelation_target state
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

example [NeZero 64] (state : State 64) :
    ∃ source' target',
      evalWordProg state (.skip : WordProg (Word 64)) = some source' ∧
      evalWordProg state
          (wordApplyColour (wordFindVar ({ vars := [] } : WordContext))
            (.skip : WordProg (Word 64))) = some target' ∧
      WordColourStateRelation (wordFindVar ({ vars := [] } : WordContext))
        source' target' := by
  let context : WordContext := { vars := [] }
  have halloc : wordAllocateProgramWithClashTreeAndColour []
      (.skip : WordProg (Word 64)) = some (context, .skip) := by
    simp [wordAllocateProgramWithClashTreeAndColour,
      wordAllocateContextWithClashes, wordAllocateVarsWithClashes,
      wordGreedyColour, wordColouringUsesAllocatable,
      wordColouringRespectsClashes, wordClashTreeAnalyze, wordClashTree,
      wordProgVariables, wordProgReadVars, wordProgWriteVars, wordClashPairs,
      wordListUnion, wordApplyColour, context]
  have hvalid : wordColourValid (wordFindVar context) := by
    intro name hname
    simpa [context, wordFindVar, lookupNatInfo] using hname
  have hinjective : Function.Injective (wordFindVar context) := by
    intro left right hcolour
    simpa [context, wordFindVar, lookupNatInfo] using hcolour
  have hzero : wordFindVar context 0 = 0 := by
    simp [context, wordFindVar, lookupNatInfo]
  have hscratch : ∀ name, name < 31 → wordFindVar context name ≠ 31 := by
    intro name hname
    simp [context, wordFindVar, lookupNatInfo]
    omega
  have hrelation : WordColourStateRelation (wordFindVar context) state state := by
    constructor
    · rfl
    · rfl
    · rfl
    · rfl
    · intro name hname hcolour
      simp [context, wordFindVar, lookupNatInfo]
  have hresult := wordAllocateProgramWithClashTreeAndColour_straightLine_simulation
    [] (.skip : WordProg (Word 64)) context .skip halloc hvalid hinjective hzero
    hscratch state state hrelation .skip
  simpa [context, wordApplyColour] using hresult

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordProg state
          (.ite .equal 1 (.reg 1) (.assign 3 (.var 1))
            (.assign 4 (.var 1))) = some source' ∧
      evalWordProg (testTargetState state)
          (wordApplyColour testColour
            (.ite .equal 1 (.reg 1) (.assign 3 (.var 1))
              (.assign 4 (.var 1)))) = some target' ∧
      testRelation source' target' := by
  apply evalWordProg_ite_applyColour testColour testColourValidFn
    testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state) (testRelation_target state)
    .equal 1 (.reg 1) true (by omega) (by intro name h; cases h; omega)
  · simp [evalWordCondition, registerOfNat]
  · exact .assign 3 1 (by omega) (by omega)
  · exact .assign 4 1 (by omega) (by omega)

example [NeZero width] (state : State width) :
    evalWordFunction state
        (.seq (.assign 3 (.var 1)) (.assign 4 (.var 3))) =
      (evalWordProg state
        (.seq (.assign 3 (.var 1)) (.assign 4 (.var 3)))).map
          (fun state => (state, [])) := by
  exact evalWordFunction_wordVarStraightLine_eq_evalWordProg state _
    (.seq (.assign 3 1 (by omega) (by omega))
      (.assign 4 3 (by omega) (by omega)))

example [NeZero width] (state : State width) :
    ∃ source' target',
      evalWordFunction state
          (.seq (.assign 3 (.var 1)) (.assign 4 (.var 3))) =
        some (source', []) ∧
      evalWordFunction (testTargetState state)
          (wordApplyColour testColour
            (.seq (.assign 3 (.var 1)) (.assign 4 (.var 3)))) =
        some (target', []) ∧
      testRelation source' target' := by
  apply evalWordFunction_wordVarStraightLine_applyColour testColour
    testColourValidFn testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state) (testRelation_target state)
  exact .seq (.assign 3 1 (by omega) (by omega))
    (.assign 4 3 (by omega) (by omega))

/-! A concrete call-colouring regression: the source passes register 1 and
    the coloured target passes register 2, while the caller relation and the
    callee effects are both preserved. -/

def colouredCallSourceState : State 8 :=
  writeRegister (zeroState 8) 1 9

def colouredCallTargetState : State 8 :=
  testTargetState colouredCallSourceState

def colouredCallSourceCallee : State 8 :=
  writeRegister (clearWordRegisters colouredCallSourceState) 1 9

def colouredCallTargetCallee : State 8 :=
  writeRegister (clearWordRegisters colouredCallTargetState) 2 9

def colouredCallSourceBody : WordProg (Word 8) :=
  .return 0 [1]

def colouredCallTargetBody : WordProg (Word 8) :=
  .return 0 [2]

def colouredCallHandler : FunName → Word 8 → Word 8 → Word 8 → Word 8 →
    State 8 → Option (State 8) :=
  fun _ _ _ _ _ state => some state

example :
    evalWordCallWithHandlersAndFfi
        [(7, [1], colouredCallSourceBody)] colouredCallHandler 2
        colouredCallSourceState none (some 7) [1] none =
      some (.returned
        { colouredCallSourceState with
          memory := colouredCallSourceCallee.memory
          privilege := colouredCallSourceCallee.privilege
          mode := colouredCallSourceCallee.mode } [9]) ∧
    evalWordCallWithHandlersAndFfi
        [(7, [2], colouredCallTargetBody)] colouredCallHandler 2
        colouredCallTargetState none (some 7) [2] none =
      some (.returned
        { colouredCallTargetState with
          memory := colouredCallTargetCallee.memory
          privilege := colouredCallTargetCallee.privilege
          mode := colouredCallTargetCallee.mode } [9]) ∧
    testRelation
      { colouredCallSourceState with
        memory := colouredCallSourceCallee.memory
        privilege := colouredCallSourceCallee.privilege
        mode := colouredCallSourceCallee.mode }
      { colouredCallTargetState with
        memory := colouredCallTargetCallee.memory
        privilege := colouredCallTargetCallee.privilege
        mode := colouredCallTargetCallee.mode } ∧
    ([9] : List (Word 8)) = [9] := by
  apply evalWordCallWithHandlersAndFfi_return_applyColour_general
    (colour := testColour)
    (sourceFunctions := [(7, [1], colouredCallSourceBody)])
    (targetFunctions := [(7, [2], colouredCallTargetBody)])
    (sourceHandler := colouredCallHandler)
    (targetHandler := colouredCallHandler)
    (fuel := 1) (functionLabel := 7)
    (parameters := [1]) (arguments := [1]) (colouredArguments := [2])
    (argumentValues := [9])
    (sourceBody := colouredCallSourceBody)
    (targetBody := colouredCallTargetBody)
    (sourceState := colouredCallSourceState)
    (targetState := colouredCallTargetState)
    (sourceCallee := colouredCallSourceCallee)
    (targetCallee := colouredCallTargetCallee)
    (sourceBodyState := colouredCallSourceCallee)
    (targetBodyState := colouredCallTargetCallee)
    (sourceValues := [9]) (targetValues := [9])
  · simp [lookupWordFunction, colouredCallSourceBody]
  · simp [lookupWordFunction, colouredCallTargetBody, testColour]
  · simp [colouredCallSourceState, readWordRegisters, registerOfNat,
      readRegister, writeRegister, zeroState]
  · simp [colouredCallTargetState, testTargetState, readWordRegisters,
      colouredCallSourceState, registerOfNat, readRegister, writeRegister,
      zeroState]
  · simp [bindWordRegisters, clearWordRegisters, colouredCallSourceState,
      colouredCallSourceCallee, registerOfNat, writeRegister]
  · simp [bindWordRegisters, clearWordRegisters, colouredCallTargetState,
      colouredCallTargetCallee, testTargetState, registerOfNat, writeRegister,
      testColour]
  · simp [colouredCallSourceBody, colouredCallSourceCallee,
      colouredCallSourceState,
      evalWordFunctionWithHandlersAndFfi, registerOfNat,
      readRegister, writeRegister, clearWordRegisters, zeroState]
  · simp [colouredCallTargetBody, colouredCallTargetCallee,
      colouredCallTargetState,
      evalWordFunctionWithHandlersAndFfi, registerOfNat,
      readRegister, writeRegister, clearWordRegisters]
  · exact testRelation_target colouredCallSourceState
  · have hcallee : colouredCallTargetCallee =
        testTargetState colouredCallSourceCallee := by
      dsimp [colouredCallTargetCallee, colouredCallTargetState,
        colouredCallSourceCallee, colouredCallSourceState, writeRegister,
        clearWordRegisters, testTargetState]
      congr
      funext register
      by_cases hone : register = 1
      · subst register
        simp
      · by_cases htwo : register = 2
        · subst register
          simp
        · simp [hone, htwo]
    rw [hcallee]
    exact testRelation_target colouredCallSourceCallee
  · rfl

example (state : State 64) :
    ∃ source' target',
      evalWordProg state
          (.assign 3 (.op .add [.var 1, .var 2])) = some source' ∧
      executeInstructions (testTargetState state) [.add 3 2 1] = target' ∧
      testRelation source' target' := by
  exact evalWordProg_wordVarStraightLine_riscv_simulation testColour
    testColourValidFn testColour_injective testColour_zero testColour_noScratch
    state (testTargetState state) (testRelation_target state)
    (.assign 3 (.op .add [.var 1, .var 2]))
    (.assignBinary .add 3 1 2 (by omega) (by omega) (by omega))
    [.add 3 2 1] (by
      simp [wordProgToRiscV, wordApplyColour, wordApplyColourExp,
        wordExpToInstructions, wordExpToInstruction, registerOfNat,
        testColour])

end Flapjack.RiscV
