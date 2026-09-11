import Flapjack.RiscV.CorrectnessSsa

namespace Flapjack.RiscV

/-! Regression coverage for the first SSA-renaming semantic boundary. -/

example :
    (evalWordProg (zeroState 32)
      (.inst (.mem .store 1 2))).map (fun state => state.memory) =
      (evalWordProg (zeroState 32)
        (.inst (wordSsaRenameInst
          ({ current := [], next := 0 } : WordSsaState)
          (.mem .store 1 2)).2)).map (fun state => state.memory) := by
  apply evalWordProg_ssaRename_store
  · intro name
    rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32) (.inst (.mem .load 1 2)) = some source' ∧
      evalWordProg (zeroState 32)
          (.inst (wordSsaRenameInst
            ({ current := [], next := 4 } : WordSsaState)
            (.mem .load 1 2)).2) = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_load_destination
  · intro name
    rfl
  · rfl
  all_goals decide

example :
    (evalWordProg (zeroState 32)
      (.inst (.mem .store32 1 2))).map (fun state => state.memory) =
      (evalWordProg (zeroState 32)
        (.inst (wordSsaRenameInst
          ({ current := [], next := 4 } : WordSsaState)
          (.mem .store32 1 2)).2)).map (fun state => state.memory) := by
  apply evalWordProg_ssaRename_store_family
  · intro name
    rfl
  · rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32) (.inst (.arith (.div 1 2 3))) = some source' ∧
      evalWordProg (zeroState 32)
          (.inst (wordSsaRenameInst
            ({ current := [], next := 4 } : WordSsaState)
            (.arith (.div 1 2 3) : WordInst)).2) = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_div_destination
  · intro name
    rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.inst (.arith (.longMul 1 2 2 3))) = some source' ∧
      evalWordProg (zeroState 32)
          (.inst (wordSsaRenameInst
            ({ current := [], next := 4 } : WordSsaState)
            (.arith (.longMul 1 2 2 3) : WordInst)).2) = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      readRegister source' ⟨2, by decide⟩ =
        readRegister target' ⟨8, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_longMul_destinations
    (ssa := ({ current := [], next := 4 } : WordSsaState))
    (source := zeroState 32) (target := zeroState 32)
    (first := ({ current := [(1, 4)], next := 8 } : WordSsaState))
    (second := ({ current := [(2, 8), (1, 4)], next := 12 } : WordSsaState))
    (freshLeft := 4) (freshRight := 8)
    (destinationLeft := 1) (destinationRight := 2)
    (sourceLeft := 2) (sourceRight := 3)
  · rfl
  · rfl
  · intro name
    rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.inst (.arith (.addCarry 1 2 6 7 9))) = some source' ∧
      evalWordProg (zeroState 32)
          (.inst (wordSsaRenameInst
            ({ current := [], next := 4 } : WordSsaState)
            (.arith (.addCarry 1 2 6 7 9) : WordInst)).2) = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      readRegister source' ⟨2, by decide⟩ =
        readRegister target' ⟨8, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_addCarry_destinations
    (ssa := ({ current := [], next := 4 } : WordSsaState))
    (source := zeroState 32) (target := zeroState 32)
    (first := ({ current := [(1, 4)], next := 8 } : WordSsaState))
    (second := ({ current := [(2, 8), (1, 4)], next := 12 } : WordSsaState))
    (freshDestination := 4) (freshCarry := 8)
    (destination := 1) (resultCarry := 2)
    (sourceLeft := 6) (sourceRight := 7) (carryIn := 9)
  · rfl
  · rfl
  · intro name
    rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32) (.inst (.mem .load8 1 2)) = some source' ∧
      evalWordProg (zeroState 32)
          (.inst (wordSsaRenameInst
            ({ current := [], next := 4 } : WordSsaState)
            (.mem .load8 1 2 : WordInst)).2) = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_load8_destination
  · intro name
    rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32) (.inst (.mem .load16 1 2)) = some source' ∧
      evalWordProg (zeroState 32)
          (.inst (wordSsaRenameInst
            ({ current := [], next := 4 } : WordSsaState)
            (.mem .load16 1 2 : WordInst)).2) = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_load16_destination
  · intro name
    rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32) (.inst (.mem .load32 1 2)) = some source' ∧
      evalWordProg (zeroState 32)
          (.inst (wordSsaRenameInst
            ({ current := [], next := 4 } : WordSsaState)
            (.mem .load32 1 2 : WordInst)).2) = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_load32_destination
  · intro name
    rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32) (.locValue 1 17) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.locValue 1 17)).2 = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_locValue_destination
  · rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32) (.assign 1 (.var 2)) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.assign 1 (.var 2))).2 = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_assign_var_destination
  · intro name
    rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.assign 1 (.const (BitVec.ofNat 32 17))) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.assign 1 (.const (BitVec.ofNat 32 17)))).2 = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_assign_const_destination
  · rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.assign 1 (.op .add [.var 2, .var 3])) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.assign 1 (.op .add [.var 2, .var 3]))).2 = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_assign_binary_var_var_destination
  · intro name
    simp [registerOfNat, wordSsaRead, lookupNatInfo]
    split
    · simp_all
    · have hlt : ¬ name < 32 := by omega
      simp [hlt]
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.assign 1 (.op .and [.var 2, .const (BitVec.ofNat 32 15)])) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.assign 1 (.op .and [.var 2, .const (BitVec.ofNat 32 15)]))).2 =
        some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_assign_binary_var_const_destination
  · intro name
    simp [registerOfNat, wordSsaRead, lookupNatInfo]
    split
    · simp_all
    · have hlt : ¬ name < 32 := by omega
      simp [hlt]
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.assign 1 (.op .xor
            [.const (BitVec.ofNat 32 3), .const (BitVec.ofNat 32 12)])) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.assign 1 (.op .xor
              [.const (BitVec.ofNat 32 3), .const (BitVec.ofNat 32 12)]))).2 =
        some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_assign_binary_const_const_destination
  · rfl
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.assign 1 (.shift .lsl (.var 2) (.const (BitVec.ofNat 32 3)))) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.assign 1 (.shift .lsl (.var 2) (.const (BitVec.ofNat 32 3))))).2 =
        some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_assign_shift_var_const_destination
  · intro name
    simp [registerOfNat, wordSsaRead, lookupNatInfo]
    split
    · simp_all
    · have hlt : ¬ name < 32 := by omega
      simp [hlt]
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.assign 1 (.shift .lsr (.var 2) (.var 3))) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.assign 1 (.shift .lsr (.var 2) (.var 3)))).2 =
        some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_assign_shift_var_var_destination
  · intro name
    simp [registerOfNat, wordSsaRead, lookupNatInfo]
    split
    · simp_all
    · have hlt : ¬ name < 32 := by omega
      simp [hlt]
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.assign 1 (.shift .ror (.var 2) (.const (BitVec.ofNat 32 3)))) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.assign 1 (.shift .ror (.var 2) (.const (BitVec.ofNat 32 3))))).2 =
        some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_assign_rotate_var_const_destination
  · intro name
    simp [registerOfNat, wordSsaRead, lookupNatInfo]
    split
    · simp_all
    · have hlt : ¬ name < 32 := by omega
      simp [hlt]
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.assign 1 (.shift .ror (.var 2) (.var 3))) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.assign 1 (.shift .ror (.var 2) (.var 3)))).2 =
        some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_assign_rotate_var_var_destination
  · intro name
    simp [registerOfNat, wordSsaRead, lookupNatInfo]
    split
    · simp_all
    · have hlt : ¬ name < 32 := by omega
      simp [hlt]
  · rfl
  all_goals decide

example :
    (evalWordProg (zeroState 32) (.store (.var 2) 1)).map
        (fun state => state.memory) =
      (evalWordProg (zeroState 32)
        (wordSsaRenameProgram
          ({ current := [], next := 4 } : WordSsaState)
          (.store (.var 2) 1)).2).map
        (fun state => state.memory) := by
  apply evalWordProg_ssaRename_program_store_var
  · intro name
    simp [registerOfNat, wordSsaRead, lookupNatInfo]
    split
    · simp_all
    · have hlt : ¬ name < 32 := by omega
      simp [hlt]
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.shareInst .load 1 (.var 2)) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.shareInst .load 1 (.var 2))).2 = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_program_share_load
  · intro name
    simp [registerOfNat, wordSsaRead, lookupNatInfo]
    split
    · simp_all
    · have hlt : ¬ name < 32 := by omega
      simp [hlt]
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.shareInst .load8 1 (.var 2)) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.shareInst .load8 1 (.var 2))).2 = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_program_share_load8
  · intro name
    simp [registerOfNat, wordSsaRead, lookupNatInfo]
    split
    · simp_all
    · have hlt : ¬ name < 32 := by omega
      simp [hlt]
  · rfl
  all_goals decide

example :
    ∃ source' target',
      evalWordProg (zeroState 32)
          (.shareInst .load16 1 (.var 2)) = some source' ∧
      evalWordProg (zeroState 32)
          (wordSsaRenameProgram
            ({ current := [], next := 4 } : WordSsaState)
            (.shareInst .load16 1 (.var 2))).2 = some target' ∧
      readRegister source' ⟨1, by decide⟩ =
        readRegister target' ⟨4, by decide⟩ ∧
      source'.memory = target'.memory := by
  apply evalWordProg_ssaRename_program_share_load16
  · intro name
    simp [registerOfNat, wordSsaRead, lookupNatInfo]
    split
    · simp_all
    · have hlt : ¬ name < 32 := by omega
      simp [hlt]
  · rfl
  all_goals decide

end Flapjack.RiscV
