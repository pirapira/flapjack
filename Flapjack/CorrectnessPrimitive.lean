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

end Flapjack
