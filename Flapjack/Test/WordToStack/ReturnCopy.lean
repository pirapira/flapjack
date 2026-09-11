import Flapjack.Stack

namespace Flapjack.Test

open Flapjack

/- CakeML's `num_stack_ret 1 [..,..]` is two: both values are copied from the
   previous frame, then those two temporary slots are freed before continuing. -/
example : stackNumReturnSlots 1 [10, 12] = 2 := by
  rfl

example : stackCopyReturn (α := Nat) false false 1 31 4 [10, 12] .skip =
    .seq
      (.seq (.stackLoad 31 1)
        (.seq (.stackStore 31 5)
          (.seq (.stackLoad 31 0)
            (.seq (.stackStore 31 4) .skip))))
      (.seq (.stackFree 2) .skip) := by
  rfl

/- A handler return starts copying below the handler record, preserving the
   frame layout established by `PushHandler`. -/
example : stackCopyReturn (α := Nat) true true 1 31 4 [10] .skip =
    .seq
      (.seq (.stackLoad 31 0)
        (.seq (.stackStore 31 9) .skip))
      (.seq (.stackFree 1) .skip) := by
  rfl

/- No stack-resident suffix leaves the continuation untouched. -/
example : stackCopyReturn (α := Nat) false false 1 31 4 [] (.return 2) = .return 2 := by
  rfl

end Flapjack.Test
