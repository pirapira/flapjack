import Flapjack.PanNbOp
import Flapjack.PanValueFfiSemantics
import Flapjack.Pancake.Semantics.PanSemStateEval

/-!
# Parity checks for `panSem$nb_op_def`

The direct HOL fixture in `scripts/hol-probes/pan_nb_op_probe.out` records the
four original source results.  These executable checks cover every constructor
of the source mapping.
-/

namespace Flapjack.Test.PanNbOpParity

open Flapjack

def op8 : Bool := panNbOp .op8 == 1
def op16 : Bool := panNbOp .op16 == 2
def opW : Bool := panNbOp .opW == 0
def op32 : Bool := panNbOp .op32 == 4

#guard op8
#guard op16
#guard opW
#guard op32

/-- Kernel-checked bridge: the Flapjack-specific source-shaped `panNbOp` agrees
pointwise with the exact tagged HOL port `nbOpHOL` (`nb_op_def`). -/
theorem panNbOp_eq_nbOpHOL : panNbOp = nbOpHOL := by
  funext size
  cases size <;> rfl

/-- Kernel-checked bridge: the production FFI byte-width mapping
`panValueFfiWidth` agrees pointwise with the exact tagged HOL port `nbOpHOL`
(`nb_op_def`). -/
theorem panValueFfiWidth_eq_nbOpHOL : panValueFfiWidth = nbOpHOL := by
  funext size
  cases size <;> rfl

def runChecks : IO Bool := do
  if op8 then IO.println "PASS Pan nb_op Op8"
  else IO.println "FAIL Pan nb_op Op8"
  if op16 then IO.println "PASS Pan nb_op Op16"
  else IO.println "FAIL Pan nb_op Op16"
  if opW then IO.println "PASS Pan nb_op OpW"
  else IO.println "FAIL Pan nb_op OpW"
  if op32 then IO.println "PASS Pan nb_op Op32"
  else IO.println "FAIL Pan nb_op Op32"
  pure (op8 && op16 && opW && op32)

end Flapjack.Test.PanNbOpParity
