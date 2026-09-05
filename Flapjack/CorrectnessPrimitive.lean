import Flapjack.Correctness
import Flapjack.RiscV.Correctness

/-!
The first general Loop-to-Word primitive bridge.  It connects the explicit
Loop AddCarry handler to the RISC-V six-instruction lowering, while exposing
the register and scratch contracts supplied by allocation.
-/

namespace Flapjack

theorem loopToWord_primitive_addCarry_agreement [NeZero width]
    (context : WordContext) (loopState : LoopState (RiscV.Word width))
    (state : RiscV.State width)
    (destination resultCarry left right carry : Nat)
    (destinationRegister resultCarryRegister leftRegister rightRegister
      carryRegister : Fin 32)
    (leftValue rightValue carryValue : RiscV.Word width)
    (hleft : loopState.locals left = some leftValue)
    (hright : loopState.locals right = some rightValue)
    (hcarry : loopState.locals carry = some carryValue)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hresultCarry :
      RiscV.registerOfNat (wordFindVar context resultCarry) =
        some resultCarryRegister)
    (hleft_register :
      RiscV.registerOfNat (wordFindVar context left) = some leftRegister)
    (hright_register :
      RiscV.registerOfNat (wordFindVar context right) = some rightRegister)
    (hcarry_register :
      RiscV.registerOfNat (wordFindVar context carry) = some carryRegister)
    (hleft_state : RiscV.readRegister state leftRegister = leftValue)
    (hright_state : RiscV.readRegister state rightRegister = rightValue)
    (hcarry_state : RiscV.readRegister state carryRegister = carryValue)
    (hzero : RiscV.readRegister state 0 = 0)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hresultCarry_nonzero : resultCarryRegister ≠ 0)
    (hdestination_resultCarry : destinationRegister ≠ resultCarryRegister)
    (hdestination_sourceRight : destinationRegister ≠ rightRegister)
    (hdestination_scratch : destinationRegister ≠ 31)
    (hresultCarry_scratch : resultCarryRegister ≠ 31)
    (hleft_scratch : leftRegister ≠ 31)
    (hright_scratch : rightRegister ≠ 31)
    (hcarry_scratch : carryRegister ≠ 31)
    (hdestination_name_resultCarry : destination ≠ resultCarry)
    (hdestination_name_scratch : wordFindVar context destination ≠ 31)
    (hresultCarry_name_scratch : wordFindVar context resultCarry ≠ 31)
    (hleft_name_scratch : wordFindVar context left ≠ 31)
    (hright_name_scratch : wordFindVar context right ≠ 31)
    (hcarry_name_scratch : wordFindVar context carry ≠ 31) :
    (evalLoopProgWithPrimitive RiscV.loopPrimitiveHandler 1 loopState
        (.primitive [destination, resultCarry] .addCarry [left, right, carry])).map
        (fun result =>
          ((loopResultState result).locals destination,
            (loopResultState result).locals resultCarry)) =
      (RiscV.evalWordProg state
        (loopToWordProg context
          (.primitive [destination, resultCarry] .addCarry
            [left, right, carry]))).map
        (fun result =>
          (some (RiscV.readRegister result destinationRegister),
            some (RiscV.readRegister result resultCarryRegister))) := by
  have hleft_lt : wordFindVar context left < 32 :=
    RiscV.registerOfNat_some_lt hleft_register
  have hright_lt : wordFindVar context right < 32 :=
    RiscV.registerOfNat_some_lt hright_register
  have hcarry_lt : wordFindVar context carry < 32 :=
    RiscV.registerOfNat_some_lt hcarry_register
  have hdestination_lt : wordFindVar context destination < 32 :=
    RiscV.registerOfNat_some_lt hdestination
  have hresultCarry_lt : wordFindVar context resultCarry < 32 :=
    RiscV.registerOfNat_some_lt hresultCarry
  have hleft_fin :
      (⟨wordFindVar context left, hleft_lt⟩ : Fin 32) = leftRegister := by
    have h := hleft_register
    simp [RiscV.registerOfNat, hleft_lt] at h
    exact h
  have hright_fin :
      (⟨wordFindVar context right, hright_lt⟩ : Fin 32) = rightRegister := by
    have h := hright_register
    simp [RiscV.registerOfNat, hright_lt] at h
    exact h
  have hcarry_fin :
      (⟨wordFindVar context carry, hcarry_lt⟩ : Fin 32) = carryRegister := by
    have h := hcarry_register
    simp [RiscV.registerOfNat, hcarry_lt] at h
    exact h
  have hdestination_fin :
      (⟨wordFindVar context destination, hdestination_lt⟩ : Fin 32) =
        destinationRegister := by
    have h := hdestination
    simp [RiscV.registerOfNat, hdestination_lt] at h
    exact h
  have hresultCarry_fin :
      (⟨wordFindVar context resultCarry, hresultCarry_lt⟩ : Fin 32) =
        resultCarryRegister := by
    have h := hresultCarry
    simp [RiscV.registerOfNat, hresultCarry_lt] at h
    exact h
  simp [evalLoopProgWithPrimitive, RiscV.loopPrimitiveHandler,
    loopReadLocals, loopAssignValues, updateLoopLocal,
    hleft, hright, hcarry, loopToWordProg, RiscV.evalWordProg,
    RiscV.wordArithToInstructions,
    RiscV.registerOfNat, hleft_lt, hright_lt, hcarry_lt,
    hdestination_lt, hresultCarry_lt, hleft_fin, hright_fin,
    hcarry_fin, hdestination_fin, hresultCarry_fin,
    hleft_name_scratch, hright_name_scratch, hcarry_name_scratch,
    hdestination_name_scratch, hresultCarry_name_scratch]
  have hadd := RiscV.executeInstructions_addCarry_general state
    destinationRegister resultCarryRegister leftRegister rightRegister
      carryRegister hzero hdestination_nonzero hresultCarry_nonzero
      hdestination_resultCarry hdestination_sourceRight hdestination_scratch
      hresultCarry_scratch hleft_scratch hright_scratch hcarry_scratch
  constructor
  · simpa [loopResultState, updateLoopLocal,
      hdestination_name_resultCarry, hleft_state, hright_state, hcarry_state] using
      (congrArg Prod.fst hadd).symm
  · simpa [loopResultState, updateLoopLocal,
      hdestination_name_resultCarry, hleft_state, hright_state, hcarry_state] using
      (congrArg Prod.snd hadd).symm

def loopStateOfCrepLocals (locals : Nat → Option α) : LoopState α :=
  { locals := locals, globals := fun _ => none, memory := fun _ => none }

theorem crepToLoop_primitive_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α] [Sub α]
    [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)]
    (primitive : CrepPrimitiveHandler α) (context : LoopContext α)
    (live : List Nat) (locals : Nat → Option α)
    (destinations : List Nat) (operator : PrimOp) (arguments : List Nat) :
    (evalCrepStateProgWithPrimitive primitive locals
      (.primitive destinations operator arguments)).map id =
      (evalLoopProgWithPrimitive primitive 1 (loopStateOfCrepLocals locals)
        (loopCompileProg context live
          (.primitive destinations operator arguments))).map
        (fun result =>
          ((loopResultState result).locals, loopResultValues result)) := by
  have hread : arguments.mapM locals = loopReadLocals locals arguments := by
    induction arguments with
    | nil => rfl
    | cons argument arguments ih =>
        simp [loopReadLocals, ih]
  simp only [evalCrepStateProgWithPrimitive]
  rw [hread]
  cases hargs : loopReadLocals locals arguments with
  | none =>
      have hargs' :
          loopReadLocals (loopStateOfCrepLocals locals).locals arguments = none := by
        simpa [loopStateOfCrepLocals] using hargs
      simp [hargs', loopCompileProg, evalLoopProgWithPrimitive]
  | some values =>
      cases hprimitive : primitive operator values with
      | none =>
          have hargs' :
              loopReadLocals (loopStateOfCrepLocals locals).locals arguments =
                some values := by
            simpa [loopStateOfCrepLocals] using hargs
          simp [hargs, hargs', hprimitive, loopCompileProg,
            evalLoopProgWithPrimitive]
      | some result =>
          have hargs' :
              loopReadLocals (loopStateOfCrepLocals locals).locals arguments =
                some values := by
            simpa [loopStateOfCrepLocals] using hargs
          have hfold (base : Nat → Option α) (entries : List (Nat × α)) :
              List.foldl (fun locals entry =>
                updateCrepLocal locals entry.fst entry.snd) base entries =
              List.foldl (fun locals entry =>
                updateLoopLocal locals entry.fst entry.snd) base entries := by
            induction entries generalizing base with
            | nil => rfl
            | cons entry entries ih =>
                cases entry with
                | mk name value =>
                    simp only [List.foldl]
                    rw [show updateCrepLocal base name value =
                      updateLoopLocal base name value by rfl]
                    exact ih _
          by_cases hlength : destinations.length = result.length
          · simp [hargs, hargs', hprimitive, hlength, loopCompileProg,
              evalLoopProgWithPrimitive, assignCrepValues, loopAssignValues,
              loopStateOfCrepLocals, loopResultState, loopResultValues, hfold,
              updateCrepLocal, updateLoopLocal]
          · simp [hargs, hargs', hprimitive, hlength, loopCompileProg,
              evalLoopProgWithPrimitive, assignCrepValues, loopAssignValues,
              loopStateOfCrepLocals, loopResultState, loopResultValues, hfold,
              updateCrepLocal, updateLoopLocal]

theorem addCarry_preserves_mapped_locals [NeZero width]
    (context : WordContext) (locals : Nat → Option (RiscV.Word width))
    (state : RiscV.State width)
    (destination resultCarry left right carry : Nat)
    (destinationRegister resultCarryRegister leftRegister rightRegister
      carryRegister : Fin 32)
    (leftValue rightValue carryValue : RiscV.Word width)
    (hlocals : loopLocalsMappedToRiscV context locals state)
    (hleft : locals left = some leftValue)
    (hright : locals right = some rightValue)
    (hcarry : locals carry = some carryValue)
    (hdestination :
      RiscV.registerOfNat (wordFindVar context destination) =
        some destinationRegister)
    (hresultCarry :
      RiscV.registerOfNat (wordFindVar context resultCarry) =
        some resultCarryRegister)
    (hleft_register :
      RiscV.registerOfNat (wordFindVar context left) = some leftRegister)
    (hright_register :
      RiscV.registerOfNat (wordFindVar context right) = some rightRegister)
    (hcarry_register :
      RiscV.registerOfNat (wordFindVar context carry) = some carryRegister)
    (hleft_state : RiscV.readRegister state leftRegister = leftValue)
    (hright_state : RiscV.readRegister state rightRegister = rightValue)
    (hcarry_state : RiscV.readRegister state carryRegister = carryValue)
    (hzero : RiscV.readRegister state 0 = 0)
    (hdestination_nonzero : destinationRegister ≠ 0)
    (hresultCarry_nonzero : resultCarryRegister ≠ 0)
    (hdestination_resultCarry : destinationRegister ≠ resultCarryRegister)
    (hdestination_sourceRight : destinationRegister ≠ rightRegister)
    (hdestination_scratch : destinationRegister ≠ 31)
    (hresultCarry_scratch : resultCarryRegister ≠ 31)
    (hleft_scratch : leftRegister ≠ 31)
    (hright_scratch : rightRegister ≠ 31)
    (hcarry_scratch : carryRegister ≠ 31)
    (hdestination_name_resultCarry : destination ≠ resultCarry)
    (hnoalias :
      ∀ name, name ≠ destination → name ≠ resultCarry →
        ∀ register,
          RiscV.registerOfNat (wordFindVar context name) = some register →
          register ≠ destinationRegister ∧
            register ≠ resultCarryRegister ∧ register ≠ 31) :
    loopLocalsMappedToRiscV context
      (updateLoopLocal
        (updateLoopLocal locals destination
          (RiscV.addCarryWords leftValue rightValue carryValue).1)
        resultCarry (RiscV.addCarryWords leftValue rightValue carryValue).2)
      (RiscV.executeInstructions state
        [.sltu 31 0 carryRegister,
          .add destinationRegister leftRegister rightRegister,
          .sltu resultCarryRegister destinationRegister rightRegister,
          .add destinationRegister destinationRegister 31,
          .sltu 31 destinationRegister 31,
          .or resultCarryRegister resultCarryRegister 31]) := by
  have hadd := RiscV.executeInstructions_addCarry_general state
    destinationRegister resultCarryRegister leftRegister rightRegister
      carryRegister hzero hdestination_nonzero hresultCarry_nonzero
      hdestination_resultCarry hdestination_sourceRight hdestination_scratch
      hresultCarry_scratch hleft_scratch hright_scratch hcarry_scratch
  intro name current hcurrent
  by_cases hname_destination : name = destination
  · subst name
    have hvalue :
        (RiscV.addCarryWords leftValue rightValue carryValue).1 = current := by
      simpa [updateLoopLocal, hdestination_name_resultCarry] using hcurrent
    subst current
    refine ⟨destinationRegister, hdestination, ?_⟩
    simpa [hleft_state, hright_state, hcarry_state] using congrArg Prod.fst hadd
  · by_cases hname_resultCarry : name = resultCarry
    · subst name
      have hvalue :
          (RiscV.addCarryWords leftValue rightValue carryValue).2 = current := by
        simpa [updateLoopLocal, hname_destination] using hcurrent
      subst current
      refine ⟨resultCarryRegister, hresultCarry, ?_⟩
      simpa [hleft_state, hright_state, hcarry_state] using congrArg Prod.snd hadd
    · have hcurrent' : locals name = some current := by
        simpa [updateLoopLocal, hname_destination, hname_resultCarry] using hcurrent
      rcases hlocals name current hcurrent' with
        ⟨register, hregister, hregister_value⟩
      refine ⟨register, hregister, ?_⟩
      have hnonalias := hnoalias name hname_destination hname_resultCarry
        register hregister
      have hzero_value : state.registers 0 = 0 := by
        simpa [RiscV.readRegister] using hzero
      have hpreserved :
          RiscV.readRegister
              (RiscV.executeInstructions state
                [.sltu 31 0 carryRegister,
                  .add destinationRegister leftRegister rightRegister,
                  .sltu resultCarryRegister destinationRegister rightRegister,
                  .add destinationRegister destinationRegister 31,
                  .sltu 31 destinationRegister 31,
                  .or resultCarryRegister resultCarryRegister 31]) register =
            RiscV.readRegister state register := by
        by_cases hzero_register : register = 0
        · subst register
          simp [RiscV.executeInstructions, RiscV.execute,
            RiscV.writeRegister, RiscV.readRegister,
            hdestination_nonzero, hresultCarry_nonzero,
            hdestination_resultCarry, hdestination_sourceRight,
            hdestination_scratch, hresultCarry_scratch,
            hleft_scratch, hright_scratch, hcarry_scratch,
            Ne.symm hdestination_resultCarry,
            Ne.symm hdestination_sourceRight,
            Ne.symm hdestination_scratch,
            Ne.symm hresultCarry_scratch,
            Ne.symm hleft_scratch, Ne.symm hright_scratch,
            Ne.symm hcarry_scratch,
            hzero_value, hnonalias.1, hnonalias.2.1, hnonalias.2.2,
            Ne.symm hnonalias.1, Ne.symm hnonalias.2.1,
            Ne.symm hnonalias.2.2]
        · simp [RiscV.executeInstructions, RiscV.execute,
            RiscV.writeRegister, RiscV.readRegister, hzero_register,
            hdestination_nonzero, hresultCarry_nonzero,
            hdestination_resultCarry, hdestination_sourceRight,
            hdestination_scratch, hresultCarry_scratch,
            hleft_scratch, hright_scratch, hcarry_scratch,
            Ne.symm hdestination_resultCarry,
            Ne.symm hdestination_sourceRight,
            Ne.symm hdestination_scratch,
            Ne.symm hresultCarry_scratch,
            Ne.symm hleft_scratch, Ne.symm hright_scratch,
            Ne.symm hcarry_scratch,
            hzero_value, hnonalias.1, hnonalias.2.1, hnonalias.2.2,
            Ne.symm hnonalias.1, Ne.symm hnonalias.2.1,
            Ne.symm hnonalias.2.2]
      exact hpreserved.trans hregister_value

end Flapjack
