import Flapjack.RiscV.Allocator
import Flapjack.RiscV.Backend

/-!
Semantic foundations for the SSA and colouring stages of the Word allocator.
The register correspondence is deliberately expressed as an `Option`-valued
equation: it covers both valid RISC-V register names and the evaluator's
failure result for out-of-range virtual names.
-/

namespace Flapjack

open RiscV

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

end Flapjack
