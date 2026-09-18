import Flapjack.PanToCrepCorrectnessBoundary

namespace Flapjack.Test.PanValuePcControlSafety

open Flapjack

def controlContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

/-! The primitive control leaves satisfy the exact top-level Cake label rule. -/
example : PanValueCrepProgramStateControlSafe (.break : Prog Nat) :=
  panValueCrepProgramStateControlSafe_break

example : PanValueCrepProgramStateControlSafe (.continue : Prog Nat) :=
  panValueCrepProgramStateControlSafe_continue

/-! Nonzero labels remain rejected at the `pc_compile_correct` boundary. -/
example :
    ¬ panValuePcResultRel [] controlContext (fun _ _ _ => True) (fun _ => some 0)
        (fun _ _ => none)
        (.broke (fun _ => none) (fun _ => none) (fun _ => none))
        (.broke { locals := fun _ => none, memory := fun _ => none } 1) := by
  apply panValuePcResultRel_broke_rejects_nonzero_label
  decide

end Flapjack.Test.PanValuePcControlSafety
