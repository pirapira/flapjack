import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect

/-! Regression cases paired with
`scripts/hol-probes/pan_structs_compile_correct_probe.out`. -/

namespace Flapjack.Test

open Flapjack

example :
    panStructConvertValue
      (.nStruct "Pair" [("left", .word 3), ("right", .word 5)]) =
        .rStruct [.word 3, .word 5] := by
  simp [panStructConvertValue, panStructConvertFieldValues]

example (context : StructPassContext) :
    structCompileProg context (.skip : Prog Nat) = .skip := by
  exact panStructCompileSkip_eq_skip context

end Flapjack.Test
