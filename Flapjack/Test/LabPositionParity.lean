import Flapjack.RiscV.Lab

namespace Flapjack.RiscV

/-! CakeML's `lab_to_target` indexes CallFFI targets from the original
    `ffi_names` order, and the exported prefix preserves that order.  These
    two-service guards exercise the position base and prefix ordering; the
    one-service case cannot distinguish the two conventions. -/

example :
    labFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "first" 64 =
      some (0 - BitVec.ofNat 64 128) := by
  decide

example :
    labFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "second" 64 =
      some (0 - BitVec.ofNat 64 112) := by
  decide

example :
    labFfiStubPrefix (width := 64)
      { services := [("first", 7), ("second", 8)] } =
      labFfiServiceStub 7 ++ labFfiServiceStub 8 ++
        List.replicate 8 (.jal 0 0) := by
  rfl

example :
    labCompileAsmWithHalt (width := 64) { services := [] } (labLabelIndexOf []) 64 999 .halt =
      some [.jal 0 (0 - BitVec.ofNat 64 80)] := by
  rfl

example :
    labCompileAsmWithHalt (width := 64) { services := [] } (labLabelIndexOf []) 64 999 .install =
      some [.jal 0 (0 - BitVec.ofNat 64 96)] := by
  rfl

example :
    labCompileAsmProgramWithFfiBaseAndHalt (width := 64)
      { services := [("first", 7), ("second", 8)] } (labLabelIndexOf []) 96 64 999
      (.callFfi "first") =
      /- Cake addresses the exported FFI block from the linked absolute
         position; `ffiBase` is retained only for the legacy API shape. -/
      some [.jal 0 (0 - BitVec.ofNat 64 160)] := by
  decide

/-! Cake can retain a LabAsm length of 5 after `add_nop`: its one-instruction
    body is followed by one complete encoded Skip even though the logical line
    length is not instruction-aligned. -/
def storedLengthFiveOracle : Bool :=
    labPadStoredInstructions (width := 64)
      [.ori 10 0 (BitVec.ofNat 64 1)] 5 ==
    [.ori 10 0 (BitVec.ofNat 64 1)]

#guard storedLengthFiveOracle

/-! Cake's `pad_section` applies each nonzero retained label length to the
    most recent prior LabAsm, appending one complete encoded Skip. -/
def twoStoredLabelPadsOracle : Bool :=
  labCompileProgramLinesWithStoredLengths (width := 64) { services := [] } (labLabelIndexOf [])
      1000 1000 2000
      [.asm (.const 1 1) [] 4,
       .label 0 1 1,
       .asm (.const 2 2) [] 4,
       .label 0 2 1] ==
    some [.ori 1 0 (BitVec.ofNat 64 1), .addi 0 0 0,
      .ori 2 0 (BitVec.ofNat 64 2), .addi 0 0 0]

#guard twoStoredLabelPadsOracle

/-! A leading retained label has no preceding Asm/LabAsm, so Cake's
    `pad_section` leaves the section physically unchanged.  Consecutive
    retained labels still apply `add_nop` to that same nearest predecessor. -/
def leadingStoredLabelNoPadOracle : Bool :=
    labCompileProgramLinesWithStoredLengths (width := 64) { services := [] } (labLabelIndexOf [])
      1000 1000 2000
      [.label 0 1 1,
       .asm (.const 1 1) [] 4] ==
    some [.ori 1 0 (BitVec.ofNat 64 1)]

#guard leadingStoredLabelNoPadOracle

def consecutiveStoredLabelPadsOracle : Bool :=
    labCompileProgramLinesWithStoredLengths (width := 64) { services := [] } (labLabelIndexOf [])
      1000 1000 2000
      [.asm (.const 1 1) [] 4,
       .label 0 1 1,
       .label 0 2 1] ==
    some [.ori 1 0 (BitVec.ofNat 64 1), .addi 0 0 0, .addi 0 0 0]

#guard consecutiveStoredLabelPadsOracle


example :
    labLinkedFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "first" 96 =
      some (0 - BitVec.ofNat 64 80) := by
  decide

example :
    labLinkedFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "second" 96 =
      some (0 - BitVec.ofNat 64 96) := by
  decide

/-! Cake's `riscv_ast` materializes ordinary immediate comparisons, including
    zero, in the encoder temporary before emitting the branch. -/
example :
    labWordConditionOperands (width := 64) .notEqual 10 (.imm 0) =
      some (10, 31, [.ori 31 0 (BitVec.ofNat 64 0)]) := by
  decide

/-! `labLookupProgramPosition` used to scan the label list linearly and take
    the first match.  The `LabLabelIndex` sptree analogue must agree with that
    scan on every key, including the duplicate entries the fixpoint sweep
    produces, where the *earlier* entry wins. -/

/-- The linear first-match scan the index replaced. -/
def labLookupProgramPositionLinear (sectionId label : Nat)
    (entries : List (Nat × Nat × Nat)) : Option Nat :=
  match entries with
  | [] => none
  | (s, l, position) :: rest =>
      if s == sectionId && l == label then some position
      else labLookupProgramPositionLinear sectionId label rest

def labIndexSampleEntries : List (Nat × Nat × Nat) :=
  [(3, 0, 1000), (3, 1, 1016), (4, 0, 1032),
   /- a stale duplicate from an earlier sweep: the first entry must win -/
   (3, 1, 9999), (4, 2, 1048), (0, 0, 812)]

def labIndexAgreesWithLinear : Bool :=
  let index := labLabelIndexOf labIndexSampleEntries
  (List.range 6).all fun sectionId =>
    (List.range 4).all fun label =>
      labLookupProgramPosition sectionId label index ==
        labLookupProgramPositionLinear sectionId label labIndexSampleEntries

#guard labIndexAgreesWithLinear

/-! Duplicate keys: the earlier entry wins, matching the first-match scan. -/
#guard labLookupProgramPosition 3 1 (labLabelIndexOf labIndexSampleEntries) ==
  some 1016

/-! A known section with an unknown label is `none`, not the section's other
    position -- the two-level tree must not collapse the label dimension. -/
#guard labLookupProgramPosition 3 2 (labLabelIndexOf labIndexSampleEntries) ==
  none

/-! An unknown section is `none`. -/
#guard labLookupProgramPosition 7 0 (labLabelIndexOf labIndexSampleEntries) ==
  none

/-! The index retains the entry list verbatim, so passes that re-emit the
    collected labels are unaffected by the change of carrier. -/
#guard (labLabelIndexOf labIndexSampleEntries).entries == labIndexSampleEntries

end Flapjack.RiscV
