import Flapjack.Compiler.Backend.WordInst.ExecutablePullExp

/-! Independent original-HOL pull_exp regression cases. Every expected native
expression below is transcribed from the fresh registered HOL EVAL output;
none is computed by calling the logical pullExp in the test. Kernel reduction
checks full expression equality; runtime checks retain every constructor,
operator, store name, operand order and native word value in the observation.
These regressions do not establish HOL-to-Lean equivalence. -/

namespace Flapjack.Test.WordInstPullExpExecutableParity
open Flapjack Flapjack.Compiler.Backend.WordInst.ExecutablePullExp

/-- Test-only complete structural observation; no field is discarded. -/
private def view {width : Nat} : WordLangExpHOL (BitVec width) → String
  | .const w => "C(" ++ toString w.toNat ++ ")"
  | .var n => "V(" ++ toString n ++ ")"
  | .lookup s => "K(" ++ reprStr s ++ ")"
  | .load e => "L(" ++ view e ++ ")"
  | .op op ls => "O(" ++ reprStr op ++ ":[" ++
      String.intercalate "," (ls.attach.map (fun e => view e.val)) ++ "])"
  | .shift sh e n => "S(" ++ reprStr sh ++ ":" ++ view e ++ "," ++ view n ++ ")"
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem e.property; omega)

-- Original capture: add_empty
example : pullExpExecutable (.op .add [] : WordLangExpHOL (BitVec 64)) =
    .const 0 := by with_unfolding_all rfl

-- Original capture: and_empty
example : pullExpExecutable (.op .and [] : WordLangExpHOL (BitVec 64)) =
    .const 0xFFFFFFFFFFFFFFFF := by with_unfolding_all rfl

-- Original capture: or_empty
example : pullExpExecutable (.op .or [] : WordLangExpHOL (BitVec 64)) =
    .const 0 := by with_unfolding_all rfl

-- Original capture: xor_empty
example : pullExpExecutable (.op .xor [] : WordLangExpHOL (BitVec 64)) =
    .const 0 := by with_unfolding_all rfl

-- Original capture: sub_empty
example : pullExpExecutable (.op .sub [] : WordLangExpHOL (BitVec 64)) =
    .op .sub [] := by with_unfolding_all rfl

-- Original capture: sub_single
example : pullExpExecutable (.op .sub [.const 5] : WordLangExpHOL (BitVec 64)) =
    .op .sub [.const 5] := by with_unfolding_all rfl

-- Original capture: sub_pair
example : pullExpExecutable (.op .sub [.const 9, .const 4] : WordLangExpHOL (BitVec 64)) =
    .const 5 := by with_unfolding_all rfl

-- Original capture: sub_var_const
example : pullExpExecutable (.op .sub [.var 1, .const 3] : WordLangExpHOL (BitVec 64)) =
    .op .add [.const 0xFFFFFFFFFFFFFFFD, .var 1] := by with_unfolding_all rfl

-- Original capture: sub_three
example : pullExpExecutable (.op .sub [.const 9, .const 4, .const 2] : WordLangExpHOL (BitVec 64)) =
    .op .sub [.const 9, .const 4, .const 2] := by with_unfolding_all rfl

-- Original capture: add_constants
example : pullExpExecutable (.op .add [.const 3, .const 5, .const 7] : WordLangExpHOL (BitVec 64)) =
    .op .add [.const 15] := by with_unfolding_all rfl

-- Original capture: add_mixed
example : pullExpExecutable (.op .add [.var 1, .const 3, .var 2, .const 5, .var 3] : WordLangExpHOL (BitVec 64)) =
    .op .add [.const 8, .var 1, .var 2, .var 3] := by with_unfolding_all rfl

-- Original capture: add_no_constants
example : pullExpExecutable (.op .add [.var 1, .var 2, .var 3] : WordLangExpHOL (BitVec 64)) =
    .op .add [.var 1, .var 2, .var 3] := by with_unfolding_all rfl

-- Original capture: nested_add
example : pullExpExecutable (.op .add [.var 1, .op .add [.const 3, .var 2], .const 5] : WordLangExpHOL (BitVec 64)) =
    .op .add [.const 8, .var 1, .var 2] := by with_unfolding_all rfl

-- Original capture: xor_cancel
example : pullExpExecutable (.op .xor [.var 1, .const 7, .const 7] : WordLangExpHOL (BitVec 64)) =
    .var 1 := by with_unfolding_all rfl

-- Original capture: and_zero
example : pullExpExecutable (.op .and [.var 1, .const 0] : WordLangExpHOL (BitVec 64)) =
    .const 0 := by with_unfolding_all rfl

-- Original capture: and_all_ones
example : pullExpExecutable (.op .and [.var 1, .const 0xFFFFFFFFFFFFFFFF] : WordLangExpHOL (BitVec 64)) =
    .op .and [.const 0xFFFFFFFFFFFFFFFF, .var 1] := by with_unfolding_all rfl

-- Original capture: or_constants
example : pullExpExecutable (.op .or [.const 3, .const 8] : WordLangExpHOL (BitVec 64)) =
    .op .or [.const 11] := by with_unfolding_all rfl

-- Original capture: xor_constants
example : pullExpExecutable (.op .xor [.const 3, .const 5] : WordLangExpHOL (BitVec 64)) =
    .op .xor [.const 6] := by with_unfolding_all rfl

-- Original capture: load_nested
example : pullExpExecutable (.load (.op .add [.var 1, .const 16]) : WordLangExpHOL (BitVec 64)) =
    .load (.op .add [.const 16, .var 1]) := by with_unfolding_all rfl

-- Original capture: shift_nested
example : pullExpExecutable (.shift .lsl (.op .xor [.const 3, .const 5]) (.const 2) : WordLangExpHOL (BitVec 64)) =
    .shift .lsl (.op .xor [.const 6]) (.const 2) := by with_unfolding_all rfl

-- Original capture: lookup
example : pullExpExecutable (.lookup .currHeap : WordLangExpHOL (BitVec 64)) =
    .lookup .currHeap := by with_unfolding_all rfl

-- Original capture: width1_wrap
example : pullExpExecutable (.op .add [.const 1, .const 1] : WordLangExpHOL (BitVec 1)) =
    .const 0 := by with_unfolding_all rfl

-- Original capture: width32_wrap
example : pullExpExecutable (.op .add [.const 0xFFFFFFFF, .const 1] : WordLangExpHOL (BitVec 32)) =
    .const 0 := by with_unfolding_all rfl

-- Original capture: width64_wrap
example : pullExpExecutable (.op .add [.const 0xFFFFFFFFFFFFFFFF, .const 1] : WordLangExpHOL (BitVec 64)) =
    .const 0 := by with_unfolding_all rfl

private def checks : List (String × Bool) := [
  ("add_empty", view (pullExpExecutable (.op .add [] : WordLangExpHOL (BitVec 64))) ==
    view (.const 0 : WordLangExpHOL (BitVec 64))),
  ("and_empty", view (pullExpExecutable (.op .and [] : WordLangExpHOL (BitVec 64))) ==
    view (.const 0xFFFFFFFFFFFFFFFF : WordLangExpHOL (BitVec 64))),
  ("or_empty", view (pullExpExecutable (.op .or [] : WordLangExpHOL (BitVec 64))) ==
    view (.const 0 : WordLangExpHOL (BitVec 64))),
  ("xor_empty", view (pullExpExecutable (.op .xor [] : WordLangExpHOL (BitVec 64))) ==
    view (.const 0 : WordLangExpHOL (BitVec 64))),
  ("sub_empty", view (pullExpExecutable (.op .sub [] : WordLangExpHOL (BitVec 64))) ==
    view (.op .sub [] : WordLangExpHOL (BitVec 64))),
  ("sub_single", view (pullExpExecutable (.op .sub [.const 5] : WordLangExpHOL (BitVec 64))) ==
    view (.op .sub [.const 5] : WordLangExpHOL (BitVec 64))),
  ("sub_pair", view (pullExpExecutable (.op .sub [.const 9, .const 4] : WordLangExpHOL (BitVec 64))) ==
    view (.const 5 : WordLangExpHOL (BitVec 64))),
  ("sub_var_const", view (pullExpExecutable (.op .sub [.var 1, .const 3] : WordLangExpHOL (BitVec 64))) ==
    view (.op .add [.const 0xFFFFFFFFFFFFFFFD, .var 1] : WordLangExpHOL (BitVec 64))),
  ("sub_three", view (pullExpExecutable (.op .sub [.const 9, .const 4, .const 2] : WordLangExpHOL (BitVec 64))) ==
    view (.op .sub [.const 9, .const 4, .const 2] : WordLangExpHOL (BitVec 64))),
  ("add_constants", view (pullExpExecutable (.op .add [.const 3, .const 5, .const 7] : WordLangExpHOL (BitVec 64))) ==
    view (.op .add [.const 15] : WordLangExpHOL (BitVec 64))),
  ("add_mixed", view (pullExpExecutable (.op .add [.var 1, .const 3, .var 2, .const 5, .var 3] : WordLangExpHOL (BitVec 64))) ==
    view (.op .add [.const 8, .var 1, .var 2, .var 3] : WordLangExpHOL (BitVec 64))),
  ("add_no_constants", view (pullExpExecutable (.op .add [.var 1, .var 2, .var 3] : WordLangExpHOL (BitVec 64))) ==
    view (.op .add [.var 1, .var 2, .var 3] : WordLangExpHOL (BitVec 64))),
  ("nested_add", view (pullExpExecutable (.op .add [.var 1, .op .add [.const 3, .var 2], .const 5] : WordLangExpHOL (BitVec 64))) ==
    view (.op .add [.const 8, .var 1, .var 2] : WordLangExpHOL (BitVec 64))),
  ("xor_cancel", view (pullExpExecutable (.op .xor [.var 1, .const 7, .const 7] : WordLangExpHOL (BitVec 64))) ==
    view (.var 1 : WordLangExpHOL (BitVec 64))),
  ("and_zero", view (pullExpExecutable (.op .and [.var 1, .const 0] : WordLangExpHOL (BitVec 64))) ==
    view (.const 0 : WordLangExpHOL (BitVec 64))),
  ("and_all_ones", view (pullExpExecutable (.op .and [.var 1, .const 0xFFFFFFFFFFFFFFFF] : WordLangExpHOL (BitVec 64))) ==
    view (.op .and [.const 0xFFFFFFFFFFFFFFFF, .var 1] : WordLangExpHOL (BitVec 64))),
  ("or_constants", view (pullExpExecutable (.op .or [.const 3, .const 8] : WordLangExpHOL (BitVec 64))) ==
    view (.op .or [.const 11] : WordLangExpHOL (BitVec 64))),
  ("xor_constants", view (pullExpExecutable (.op .xor [.const 3, .const 5] : WordLangExpHOL (BitVec 64))) ==
    view (.op .xor [.const 6] : WordLangExpHOL (BitVec 64))),
  ("load_nested", view (pullExpExecutable (.load (.op .add [.var 1, .const 16]) : WordLangExpHOL (BitVec 64))) ==
    view (.load (.op .add [.const 16, .var 1]) : WordLangExpHOL (BitVec 64))),
  ("shift_nested", view (pullExpExecutable (.shift .lsl (.op .xor [.const 3, .const 5]) (.const 2) : WordLangExpHOL (BitVec 64))) ==
    view (.shift .lsl (.op .xor [.const 6]) (.const 2) : WordLangExpHOL (BitVec 64))),
  ("lookup", view (pullExpExecutable (.lookup .currHeap : WordLangExpHOL (BitVec 64))) ==
    view (.lookup .currHeap : WordLangExpHOL (BitVec 64))),
  ("width1_wrap", view (pullExpExecutable (.op .add [.const 1, .const 1] : WordLangExpHOL (BitVec 1))) ==
    view (.const 0 : WordLangExpHOL (BitVec 1))),
  ("width32_wrap", view (pullExpExecutable (.op .add [.const 0xFFFFFFFF, .const 1] : WordLangExpHOL (BitVec 32))) ==
    view (.const 0 : WordLangExpHOL (BitVec 32))),
  ("width64_wrap", view (pullExpExecutable (.op .add [.const 0xFFFFFFFFFFFFFFFF, .const 1] : WordLangExpHOL (BitVec 64))) ==
    view (.const 0 : WordLangExpHOL (BitVec 64)))
 ]

def runChecks : IO Bool := do
  for (label, ok) in checks do
    unless ok do throw (IO.userError ("original pull_exp mismatch: " ++ label))
  IO.println "PASS executable native pull_exp: 24 independent original cases, widths 1/32/64"
  return true

end Flapjack.Test.WordInstPullExpExecutableParity
