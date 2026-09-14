import Flapjack.RiscV.WordToStack
import Flapjack.StackRemove

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
  .ite .test 2 (.reg 2)
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

/-! The code-table entries are functions.  CakeML's word-to-stack pass first
    reseats their even-numbered ABI arguments in the locations assigned to
    the helper's formal variables. -/
def cakeWordStackHelperRegister : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 4 => 7
  | 6 => 9
  | 8 => 11
  | 10 => 13
  | 11 => 15
  | 12 => 17
  | 14 => 19
  | 16 => 21
  | _ => 23

def cakeWordStackHelperConfig (program : WordProg Nat) : WordStackConfig :=
  { locations := (wordProgVariables program).eraseDups.map
      (fun name => (name, .register (cakeWordStackHelperRegister name)))
    scratch := 31
    stackBase := 0
    addressScratch := 29 }

def cakeLongDiv1StackEntryCode (config : WordStackConfig) (width : Nat) :
    Option (StackProg Nat) := do
  let body ← cakeLongDiv1StackCode config width
  let moves ← wordStackMovesFromPhysical config
    [0, 2, 4, 6, 8, 10, 12] wordStackAbiBase
  pure (wordStackJoin moves body)

def cakeLongDivStackEntryCode (config : WordStackConfig) (width : Nat) :
    Option (StackProg Nat) := do
  let body ← cakeLongDivStackCode config width
  let moves ← wordStackMovesFromPhysical config [0, 2, 4, 6] wordStackAbiBase
  pure (wordStackJoin moves body)

/-! Adapt the source helper's Loc convention to the normalized StackLang
    LongDiv convention: the caller supplies high and low in x3 and x0, the
    divisor in x6, and observes quotient x0 and remainder x3. -/
def cakeLongDivStackAdapter : StackProg Nat :=
  stackSeq [
    .arith .or (wordStackAbiBase + 6) 6 6,
    .arith .or (wordStackAbiBase + 2) 3 3,
    .arith .or (wordStackAbiBase + 4) 0 0,
    .call (some
      (stackSeq [
        .arith .or 0 wordStackAbiBase wordStackAbiBase,
        .get 3 (.temp 28)], 0, 0, 0))
      (.label cakeLongDivLocation) none]

def stackProgContainsLongDiv : StackProg Nat → Bool
  | .inst (.arith (.longDiv _ _ _ _ _)) => true
  | .seq first second => stackProgContainsLongDiv first || stackProgContainsLongDiv second
  | .ite _ _ _ thenBranch elseBranch =>
      stackProgContainsLongDiv thenBranch || stackProgContainsLongDiv elseBranch
  | .loop body => stackProgContainsLongDiv body
  | .call returnHandler _ handler =>
      (match returnHandler with
      | none => false
      | some (program, _, _, _) => stackProgContainsLongDiv program) ||
      (match handler with
      | none => false
      | some (program, _, _) => stackProgContainsLongDiv program)
  | _ => false

def stackProgExpandLongDiv : StackProg Nat → StackProg Nat
  | .inst (.arith (.longDiv _ _ _ _ _)) => cakeLongDivStackAdapter
  | .seq first second =>
      .seq (stackProgExpandLongDiv first) (stackProgExpandLongDiv second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right (stackProgExpandLongDiv thenBranch)
        (stackProgExpandLongDiv elseBranch)
  | .loop body => .loop (stackProgExpandLongDiv body)
  | .call returnHandler target handler =>
      .call
        (match returnHandler with
        | none => none
        | some (program, link, returnLabel, entryLabel) =>
            some (stackProgExpandLongDiv program, link, returnLabel, entryLabel))
        target
        (match handler with
        | none => none
        | some (program, exceptionLabel, handlerLabel) =>
            some (stackProgExpandLongDiv program, exceptionLabel, handlerLabel))
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def cakeLongDivRuntimeSections (config : StackRemoveConfig) :
    Option (List (Nat × StackProg Nat)) := do
  let width := config.bytesInWord * 8
  let helperProgram : WordProg Nat :=
    cakeWordSeq [cakeLongDivCode width, cakeLongDiv1Code width]
  let wordConfig := cakeWordStackHelperConfig helperProgram
  let longDiv1 ← cakeLongDiv1StackEntryCode wordConfig width
  let longDiv ← cakeLongDivStackEntryCode wordConfig width
  pure [(cakeLongDiv1Location, longDiv1), (cakeLongDivLocation, longDiv)]

def stackProgramsWithLongDivRuntime (config : StackRemoveConfig)
    (programs : List (Nat × StackProg Nat)) :
    Option (List (Nat × StackProg Nat)) :=
  if programs.any (fun program => stackProgContainsLongDiv program.2) then do
    let helpers ← cakeLongDivRuntimeSections config
    let expanded := programs.map (fun (sectionId, program) =>
      (sectionId, stackProgExpandLongDiv program))
    pure (helpers ++ expanded)
  else
    some programs

example : cakeLongDiv1ShiftRight 1 6 = .const 0 := by
  rfl

example : cakeLongDiv1HighShift 0 = .var 4 := by
  rfl

example : cakeLongDiv1Mask 0 = 0 := by
  decide

example : cakeLongDiv1Mask 8 = 255 := by
  decide

end Flapjack.RiscV
