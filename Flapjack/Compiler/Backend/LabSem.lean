import Flapjack.Compiler.Backend.LabLang
import Flapjack.HolRef

/-!
# Cake LabLang semantics helpers

Ports of the syntactic helpers from `cakeml/compiler/backend/semantics/labSemScript.sml`
used by the LabLang/LabProps preconditions. Currently this is `is_Label`
(`labSemScript.sml:47`), the line classifier consumed by `sec_ends_with_label`
(`labPropsScript.sml:81`).
-/

namespace Flapjack.Compiler.Backend.LabSem

open Flapjack.Compiler.Backend.LabLang

/-- HOL `labSem$is_Label_def` (`labSemScript.sml:47`): true exactly on `Label`
lines. The imported asm carriers are explicit type parameters, as elsewhere in
this tree; the classification does not inspect them. -/
@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "is_Label_def"]
def isLabel {AsmOrCbw AsmWithLab Word : Type}
    (line : Line AsmOrCbw AsmWithLab Word) : Bool :=
  match line with
  | .label _ _ _ => true
  | _ => false

end Flapjack.Compiler.Backend.LabSem