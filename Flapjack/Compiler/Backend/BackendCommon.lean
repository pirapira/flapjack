import Flapjack.HolRef

/-!
The word-arithmetic helper shared by Pancake's Pan, Crep, and Loop primitive
semantics. Its source is CakeML's `compiler/backend/backend_commonScript.sml`.
-/

namespace Flapjack

/-- HOL `backend_common$word_add_carry`: interpret any nonzero carry input as
    one, return the low word and a one-word overflow flag. The HOL word type
    always has positive width, represented here by `NeZero width`. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "word_add_carry_def"]
def wordAddCarryHOL {width : Nat} [NeZero width]
    (left right carry : BitVec width) : BitVec width × BitVec width :=
  let result := left.toNat + right.toNat + (if carry == 0 then 0 else 1)
  (BitVec.ofNat width result,
    if 2 ^ width ≤ result then BitVec.ofNat width 1 else BitVec.ofNat width 0)

/-- HOL `backend_common$stack_num_stubs`: number of stack-language stubs. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "stack_num_stubs_def"]
def stackNumStubs : Nat := 5

/-- HOL `backend_common$word_num_stubs = stack_num_stubs + 1 + 1`. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "word_num_stubs_def"]
def wordNumStubs : Nat := stackNumStubs + 1 + 1

/-- HOL `backend_common$data_num_stubs = word_num_stubs + 32 + 23`
(general and bignum stubs). -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "data_num_stubs_def"]
def dataNumStubs : Nat := wordNumStubs + 32 + 23

/-- HOL `backend_common$word_shift`: the shift amount is 2 for 32-bit words and
    3 otherwise. HOL uses `dimindex (:'a)` only through its numeric size and has
    no word-valued carrier, so Lean binds the word width explicitly. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "word_shift_def"
  (word_dimension_as_width := width)]
def wordShiftAmount (width : Nat) [NeZero width] : Nat := if width = 32 then 2 else 3

example : @wordShiftAmount 1 ⟨by decide⟩ = 3 := rfl
example : @wordShiftAmount 4 ⟨by decide⟩ = 3 := rfl
example : @wordShiftAmount 8 ⟨by decide⟩ = 3 := rfl
example : @wordShiftAmount 16 ⟨by decide⟩ = 3 := rfl
example : @wordShiftAmount 32 ⟨by decide⟩ = 2 := rfl
example : @wordShiftAmount 64 ⟨by decide⟩ = 3 := rfl
example : @wordShiftAmount 128 ⟨by decide⟩ = 3 := rfl

end Flapjack
