import Flapjack.CrepeIdentityCallCorrectness

namespace Flapjack

/-! A concrete Nat instantiation keeps the executable source/target
    declaration-call relation in the test suite. -/
theorem identity_declaration_call_relation_test :
    panValueCrepControlRel [] (correctnessIdentityContext (α := Nat))
      (fun _ _ _ => True)
      (restorePanValueControlLocal "result"
        (correctnessIdentitySourceLocals (α := Nat) "result")
        (.returned (fun _ => none) (correctnessIdentitySourceGlobals (α := Nat))
          (correctnessIdentitySourceMemory (α := Nat)) [.word 7]))
      (restoreCrepResultList
        (correctnessIdentityCrepState (α := Nat)).locals
        (allocatedNames (correctnessIdentityContext (α := Nat)) .one)
        (.returned (correctnessIdentityCallState (α := Nat) 7) [7])) := by
  exact (compile_full_pan_value_identity_declaration_call_relation
    (α := Nat) 7).2.2

end Flapjack
