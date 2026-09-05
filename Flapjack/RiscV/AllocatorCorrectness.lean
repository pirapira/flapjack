import Flapjack.RiscV.Allocator
import Flapjack.RiscV.Backend
import Flapjack.WordSemantics

/-!
Semantic foundations for the SSA and colouring stages of the Word allocator.
The register correspondence is deliberately expressed as an `Option`-valued
equation: it covers both valid RISC-V register names and the evaluator's
failure result for out-of-range virtual names.
-/

namespace Flapjack

open RiscV

def wordControlResultValues [NeZero width] :
    WordControlResult width → List (Word width)
  | .returned _ values => values
  | _ => []

theorem evalWordExp_ssaRename [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (hmemory : source.memory = target.memory)
    (expression : WordExp (Word width)) :
    evalWordExp source expression =
      evalWordExp target (wordSsaRenameExp ssa expression) := by
  cases expression with
  | const value => simp [evalWordExp, wordSsaRenameExp]
  | var name =>
      simpa [wordSsaRenameExp, evalWordExp] using hregister name
  | lookup store => simp [evalWordExp, wordSsaRenameExp]
  | load address =>
      simp only [evalWordExp, wordSsaRenameExp]
      rw [show evalWordExp source address =
          evalWordExp target (wordSsaRenameExp ssa address) from
            evalWordExp_ssaRename ssa source target hregister hmemory address]
      have hword : ∀ value, readWordValue source value =
          readWordValue target value := by
        intro value
        simp [readWordValue, readByte, hmemory]
      simp [hword]
  | op operator arguments =>
      cases arguments with
      | nil => simp [evalWordExp, wordSsaRenameExp]
      | cons left rest =>
          cases rest with
          | nil => simp [evalWordExp, wordSsaRenameExp]
          | cons right rest =>
              cases rest with
              | nil =>
                  cases left with
                  | var left =>
                      cases right with
                      | var right =>
                          simp only [wordSsaRenameExp]
                          simp only [evalWordExp]
                          cases hleft : registerOfNat left <;>
                            cases hleft' : registerOfNat (wordSsaRead ssa left) <;>
                            cases hright : registerOfNat right <;>
                            cases hright' : registerOfNat (wordSsaRead ssa right) <;>
                            all_goals
                              have hleftValue := hregister left
                              have hrightValue := hregister right
                              simp_all [hleft, hleft', hright, hright',
                                hleftValue, hrightValue, wordSsaRenameExp,
                                evalWordExp]
                      | _ => simp [evalWordExp, wordSsaRenameExp]
                  | _ => simp [evalWordExp, wordSsaRenameExp]
              | cons _ _ => simp [evalWordExp, wordSsaRenameExp]
  | shift operator left right =>
      cases left with
      | var leftName =>
          cases right with
          | var rightName =>
              simp only [wordSsaRenameExp]
              simp only [evalWordExp]
              cases hleft : registerOfNat leftName <;>
                cases hleft' : registerOfNat (wordSsaRead ssa leftName) <;>
                cases hright : registerOfNat rightName <;>
                cases hright' : registerOfNat (wordSsaRead ssa rightName) <;>
                all_goals
                  have hleftValue := hregister leftName
                  have hrightValue := hregister rightName
                  simp_all [hleft, hleft', hright, hright',
                    hleftValue, hrightValue, wordSsaRenameExp, evalWordExp]
          | const amount =>
              simp only [wordSsaRenameExp]
              simp only [evalWordExp]
              cases hleft : registerOfNat leftName <;>
                cases hleft' : registerOfNat (wordSsaRead ssa leftName) <;>
                all_goals
                  have hleftValue := hregister leftName
                  simp_all [hleft, hleft', hleftValue, wordSsaRenameExp,
                    evalWordExp]
          | _ => simp [evalWordExp, wordSsaRenameExp]
      | _ => simp [evalWordExp, wordSsaRenameExp]

theorem evalWordCondition_ssaRename [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (operator : Cmp) (condition : Nat)
    (rightValue : WordRegImm (Word width)) :
    evalWordCondition source operator condition rightValue =
      evalWordCondition target operator (wordSsaRead ssa condition)
        (wordSsaRenameRegImm ssa rightValue) := by
  cases rightValue with
  | imm value =>
      simp only [evalWordCondition, wordSsaRenameRegImm]
      cases hcondition : registerOfNat condition <;>
        cases hcondition' : registerOfNat (wordSsaRead ssa condition) <;>
        all_goals
          have hconditionValue := hregister condition
          simp_all [hcondition, hcondition', hconditionValue,
            evalWordCondition]
  | reg right =>
      simp only [evalWordCondition, wordSsaRenameRegImm]
      cases hcondition : registerOfNat condition <;>
        cases hcondition' : registerOfNat (wordSsaRead ssa condition) <;>
        cases hright : registerOfNat right <;>
        cases hright' : registerOfNat (wordSsaRead ssa right) <;>
        all_goals
          have hconditionValue := hregister condition
          have hrightValue := hregister right
          simp_all [hcondition, hcondition', hright, hright',
            hconditionValue, hrightValue, evalWordCondition,
            wordSsaRenameRegImm]

theorem evalWordReturn_ssaRename [NeZero width]
    (ssa : WordSsaState) (source target : State width)
    (hregister : ∀ name,
      (do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (do
        let register ← registerOfNat (wordSsaRead ssa name)
        pure (readRegister target register)))
    (fuel label : Nat) (values : List Nat) :
    (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) (fuel + 1) source
        (.return label values)).map wordControlResultValues =
      (evalWordFunctionWithHandlersAndFfi []
        (fun _ _ _ _ _ state => some state) (fuel + 1) target
        (.return label (values.map (wordSsaRead ssa)))).map
        wordControlResultValues := by
  have hvalues :
      values.mapM (fun name => do
        let register ← registerOfNat name
        pure (readRegister source register)) =
      (values.map (wordSsaRead ssa)).mapM (fun name => do
        let register ← registerOfNat name
        pure (readRegister target register)) := by
    induction values with
    | nil => rfl
    | cons name values ih =>
        simp only [List.map, List.mapM_cons]
        rw [hregister name, ih]
  simp only [evalWordFunctionWithHandlersAndFfi, Option.map]
  rw [hvalues]
  cases hresult : List.mapM (fun name => do
      let register ← registerOfNat name
      pure (readRegister target register)) (List.map (wordSsaRead ssa) values) with
  | none => simp [hresult]
  | some returnedValues => simp [hresult, wordControlResultValues]

end Flapjack
