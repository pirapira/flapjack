import Flapjack.RiscV.WordToStack

/-!
# CakeML software LongDiv code-table shape

This is the source-shaped WordLang helper selected by CakeML's
`LongDiv_code_def` when `has_longdiv = false`.  It is deliberately kept as a
code-table value: the RISC-V instruction selector must continue to reject a
direct Word `LongDiv`, as the original `riscv_targetScript.sml` does.

Reference: `cakeml/compiler/backend/data_to_wordScript.sml:829-867`.
-/

namespace Flapjack.RiscV

def cakeLongDiv1Location : Nat := 22

def cakeLongDivLocation : Nat := 23

def cakeWordSeq : List (WordProg Nat) → WordProg Nat
  | [] => .skip
  | [program] => program
  | program :: programs => .seq program (cakeWordSeq programs)

def cakeLongDiv1Call : WordProg Nat :=
  .call none (some cakeLongDiv1Location) [0, 2, 4, 6, 8, 10, 12] none

/- These helpers retain the static guards emitted by CakeML's HOL code table.
   They are evaluated at the target word width, so the resulting WordExp is
   the same guarded expression after specialization rather than an
   unconditional shift that is invalid at width zero or one. -/
def cakeLongDiv1ShiftRight (width source : Nat) : WordExp Nat :=
  if width ≤ 1 then .const 0 else
    .shift .lsr (.var source) (.const 1)

def cakeLongDiv1ShiftLeft (width source : Nat) : WordExp Nat :=
  if width ≤ 1 then .const 0 else
    .shift .lsl (.var source) (.const 1)

def cakeLongDiv1HighShift : Nat → WordExp Nat
  | width =>
      let amount := width - 1
      if amount = 0 then .var 4
      else if width ≤ amount then .const 0
      else .shift .lsl (.var 4) (.const amount)

def cakeLongDiv1Mask (width : Nat) : Nat :=
  let dimword := 2 ^ width
  if 1 % dimword = 0 then 0 else (dimword - 1) % dimword

def cakeLongDiv1Code (width : Nat) : WordProg Nat :=
  .ite .test 2 (.imm 1)
    (.seq (.set (.temp 28) (.var 10)) (.return 0 [8]))
    (cakeWordSeq [
      .assign 6 (.op .or [
        cakeLongDiv1ShiftRight width 6,
        cakeLongDiv1HighShift width]),
      .assign 4 (cakeLongDiv1ShiftRight width 4),
      .assign 8 (cakeLongDiv1ShiftLeft width 8),
      .assign 2 (.op .sub [.var 2, .const 1]),
      .ite .lower 12 (.reg 4) cakeLongDiv1Call .skip,
      .ite .equal 12 (.reg 4)
        (.ite .lower 10 (.reg 6) cakeLongDiv1Call .skip)
        .skip,
      .assign 8 (.op .add [.var 8, .const 1]),
      .assign 16 (.op .xor [.var 6, .const (cakeLongDiv1Mask width)]),
      .assign 14 (.op .xor [.var 4, .const (cakeLongDiv1Mask width)]),
      .assign 1 (.const 1),
      /- Cake AddCarry is explicitly four-register: r4 is both carry input
         and carry output. -/
      .inst (.arith (.cakeAddCarry 10 10 16 1)),
      .inst (.arith (.cakeAddCarry 12 12 14 1)),
      cakeLongDiv1Call])

def cakeLongDivCode (width : Nat) : WordProg Nat :=
  cakeWordSeq [
    .assign 10 (.const 0),
    .assign 11 (.const width),
    .call none (some cakeLongDiv1Location) [0, 11, 6, 10, 10, 4, 2] none]

def cakeLongDiv1StackCode (config : WordStackConfig) (width : Nat) :
    Option (StackProg Nat) :=
  wordToStackProgNat config (cakeLongDiv1Code width)

def cakeLongDivStackCode (config : WordStackConfig) (width : Nat) :
    Option (StackProg Nat) :=
  wordToStackProgNat config (cakeLongDivCode width)

example : cakeLongDiv1ShiftRight 1 6 = .const 0 := by
  rfl

example : cakeLongDiv1HighShift 0 = .var 4 := by
  rfl

example : cakeLongDiv1Mask 0 = 0 := by
  decide

example : cakeLongDiv1Mask 8 = 255 := by
  decide

end Flapjack.RiscV
