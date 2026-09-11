import Flapjack.RiscV.CorrectnessColour

/-!
# SSA-renaming to colouring boundary

CakeML's SSA pass gives each assignment a fresh destination, while the
colouring pass applies one fixed name map to a whole program.  These are the
same transformation for a straight-line assignment when its RHS does not
read the destination.  This module records that equation and immediately
feeds it into the executable colouring simulation.
-/

namespace Flapjack.RiscV

def ssaAssignmentColour (ssa : WordSsaState) (name : Nat) : Nat → Nat :=
  fun current => if current = name then (wordSsaFresh ssa name).2
    else wordSsaRead ssa current

/-! Before an SSA assignment, the destination's old value need not satisfy the
    eventual colouring relation: the generated code overwrites it. -/

structure WordColourStateRelationExcept (colour : Nat → Nat) (excluded : Nat)
    [NeZero width] (source target : State width) : Prop where
  pc : source.pc = target.pc
  memory : source.memory = target.memory
  privilege : source.privilege = target.privilege
  mode : source.mode = target.mode
  register : ∀ (current : Nat) (hcurrent : current < 32)
      (_hnot : current ≠ excluded) (hcolour : colour current < 32),
    readRegister source ⟨current, hcurrent⟩ =
      readRegister target ⟨colour current, hcolour⟩

theorem wordColourStateRelationExcept_nextPc
    (colour : Nat → Nat) (excluded : Nat)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelationExcept colour excluded source target) :
    WordColourStateRelationExcept colour excluded
      {source with pc := nextPc source} {target with pc := nextPc target} := by
  constructor
  · simp [nextPc, hrelation.pc]
  · exact hrelation.memory
  · exact hrelation.privilege
  · exact hrelation.mode
  · intro current hcurrent hnot hcolour
    exact hrelation.register current hcurrent hnot hcolour

theorem wordColourStateRelationExcept_writeRegister
    (colour : Nat → Nat) (excluded : Nat)
    (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelationExcept colour excluded source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hname : excluded < 32) (value targetValue : Word width)
    (hvalue : value = targetValue) :
    WordColourStateRelation colour
      (writeRegister source ⟨excluded, hname⟩ value)
      (writeRegister target ⟨colour excluded, valid excluded hname⟩ targetValue) := by
  by_cases hzero : excluded = 0
  · have hcolourZero : colour excluded = 0 := by simpa [hzero] using colourZero
    subst excluded
    constructor
    · simpa [writeRegister, colourZero] using hrelation.pc
    · simpa [writeRegister, colourZero] using hrelation.memory
    · simpa [writeRegister, colourZero] using hrelation.privilege
    · simpa [writeRegister, colourZero] using hrelation.mode
    · intro current hcurrent hcolour
      by_cases hcurrentZero : current = 0
      · subst current
        simpa [ZeroRegister, readRegister, writeRegister, colourZero] using
          hzeroSource.trans hzeroTarget.symm
      · simpa [writeRegister, readRegister, colourZero, hcurrentZero] using
          hrelation.register current hcurrent hcurrentZero hcolour
  · have hsourceNonzero : (⟨excluded, hname⟩ : Fin 32) ≠ 0 := by
      intro h
      exact hzero (congrArg Fin.val h)
    have hcolourNonzero : colour excluded ≠ 0 := by
      intro h
      apply hzero
      apply injective
      simpa [colourZero] using h
    have htargetNonzero :
        (⟨colour excluded, valid excluded hname⟩ : Fin 32) ≠ 0 := by
      intro h
      exact hcolourNonzero (congrArg Fin.val h)
    constructor
    · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
      exact hrelation.pc
    · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
      exact hrelation.memory
    · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
      exact hrelation.privilege
    · simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false]
      exact hrelation.mode
    · intro current hcurrent hcolour
      by_cases hsame : current = excluded
      · subst current
        have hsourceEq :
            (⟨excluded, hcurrent⟩ : Fin 32) = ⟨excluded, hname⟩ := by
          apply Fin.ext
          rfl
        have htargetEq :
            (⟨colour excluded, hcolour⟩ : Fin 32) =
              ⟨colour excluded, valid excluded hname⟩ := by
          apply Fin.ext
          rfl
        simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false,
          readRegister]
        simp only [if_true]
        exact hvalue
      · have htargetSame :
            (⟨colour current, hcolour⟩ : Fin 32) ≠
              (⟨colour excluded, valid excluded hname⟩ : Fin 32) := by
          intro h
          apply hsame
          apply injective
          exact congrArg Fin.val h
        have hsourceCurrent :
            (⟨current, hcurrent⟩ : Fin 32) ≠ ⟨excluded, hname⟩ := by
          intro h
          apply hsame
          exact congrArg Fin.val h
        simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false,
          readRegister]
        rw [if_neg hsourceCurrent, if_neg htargetSame]
        exact hrelation.register current hcurrent hsame hcolour

theorem wordColourStateRelationExcept_executeConst
    [NeZero width]
    (colour : Nat → Nat) (excluded : Nat)
    (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept colour excluded source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hname : excluded < 32) (hvalue : Word width) :
    WordColourStateRelation colour
      (execute source (.addi ⟨excluded, hname⟩ 0 hvalue))
      (execute target
        (.addi ⟨colour excluded, valid excluded hname⟩ 0 hvalue)) := by
  have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
  have hread :
      readRegister source 0 + hvalue = readRegister target 0 + hvalue := by
    simpa [ZeroRegister] using congrArg (fun value => value + hvalue)
      (hzeroSource.trans hzeroTarget.symm)
  have hstate := wordColourStateRelationExcept_writeRegister colour excluded
    valid injective colourZero {source with pc := nextPc source}
    {target with pc := nextPc target} hnext
    (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
    (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
    hname (readRegister source 0 + hvalue)
    (readRegister target 0 + hvalue) hread
  simpa [execute] using hstate

theorem wordColourStateRelationExcept_executeAddi
    [NeZero width]
    (colour : Nat → Nat) (excluded : Nat)
    (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept colour excluded source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hname : excluded < 32) (sourceName : Nat) (hsource : sourceName < 32)
    (hsourceNe : sourceName ≠ excluded) (immediate : Word width) :
    WordColourStateRelation colour
      (execute source (.addi ⟨excluded, hname⟩ ⟨sourceName, hsource⟩ immediate))
      (execute target
        (.addi ⟨colour excluded, valid excluded hname⟩
          ⟨colour sourceName, valid sourceName hsource⟩ immediate)) := by
  have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
  have hvalue :
      readRegister source ⟨sourceName, hsource⟩ + immediate =
        readRegister target ⟨colour sourceName, valid sourceName hsource⟩ + immediate := by
    rw [hrelation.register sourceName hsource hsourceNe
      (valid sourceName hsource)]
  have hstate := wordColourStateRelationExcept_writeRegister colour excluded
    valid injective colourZero {source with pc := nextPc source}
    {target with pc := nextPc target} hnext
    (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
    (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
    hname (readRegister source ⟨sourceName, hsource⟩ + immediate)
    (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ + immediate)
    hvalue
  simpa [execute] using hstate

theorem wordColourStateRelationExcept_executeBinary
    [NeZero width]
    (colour : Nat → Nat) (excluded : Nat)
    (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept colour excluded source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (operator : BinOp) (left right : Nat)
    (hname : excluded < 32) (hleft : left < 32) (hright : right < 32)
    (hleftNe : left ≠ excluded) (hrightNe : right ≠ excluded) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .add => .add ⟨excluded, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .sub => .sub ⟨excluded, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .and => .and ⟨excluded, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .or => .or ⟨excluded, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .xor => .xor ⟨excluded, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
      (execute target (match operator with
        | .add => .add ⟨colour excluded, valid excluded hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .sub => .sub ⟨colour excluded, valid excluded hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .and => .and ⟨colour excluded, valid excluded hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .or => .or ⟨colour excluded, valid excluded hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .xor => .xor ⟨colour excluded, valid excluded hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
  cases operator with
  | add =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ + readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ +
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft hleftNe (valid left hleft),
          hrelation.register right hright hrightNe (valid right hright)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname
          (readRegister source ⟨left, hleft⟩ + readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ +
            readRegister target ⟨colour right, valid right hright⟩) hvalue)

  | sub =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ - readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ -
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft hleftNe (valid left hleft),
          hrelation.register right hright hrightNe (valid right hright)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname
          (readRegister source ⟨left, hleft⟩ - readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ -
            readRegister target ⟨colour right, valid right hright⟩) hvalue)
  | and =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ &&& readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ &&&
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft hleftNe (valid left hleft),
          hrelation.register right hright hrightNe (valid right hright)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname
          (readRegister source ⟨left, hleft⟩ &&& readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ &&&
            readRegister target ⟨colour right, valid right hright⟩) hvalue)
  | or =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ ||| readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ |||
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft hleftNe (valid left hleft),
          hrelation.register right hright hrightNe (valid right hright)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname
          (readRegister source ⟨left, hleft⟩ ||| readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ |||
            readRegister target ⟨colour right, valid right hright⟩) hvalue)
  | xor =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ ^^^ readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ ^^^
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft hleftNe (valid left hleft),
          hrelation.register right hright hrightNe (valid right hright)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname
          (readRegister source ⟨left, hleft⟩ ^^^ readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ ^^^
            readRegister target ⟨colour right, valid right hright⟩) hvalue)

theorem wordColourStateRelationExcept_executeImmediateBinary
    [NeZero width]
    (colour : Nat → Nat) (excluded : Nat)
    (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept colour excluded source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (operator : BinOp) (sourceName : Nat) (value : Word width)
    (hname : excluded < 32) (hsource : sourceName < 32)
    (hsourceNe : sourceName ≠ excluded) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .add => .addi ⟨excluded, hname⟩ ⟨sourceName, hsource⟩ value
        | .sub => .addi ⟨excluded, hname⟩ ⟨sourceName, hsource⟩ (0 - value)
        | .and => .andi ⟨excluded, hname⟩ ⟨sourceName, hsource⟩ value
        | .or => .ori ⟨excluded, hname⟩ ⟨sourceName, hsource⟩ value
        | .xor => .xori ⟨excluded, hname⟩ ⟨sourceName, hsource⟩ value))
      (execute target (match operator with
        | .add => .addi ⟨colour excluded, valid excluded hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value
        | .sub => .addi ⟨colour excluded, valid excluded hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ (0 - value)
        | .and => .andi ⟨colour excluded, valid excluded hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value
        | .or => .ori ⟨colour excluded, valid excluded hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value
        | .xor => .xori ⟨colour excluded, valid excluded hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value)) := by
  cases operator with
  | add =>
      simpa using wordColourStateRelationExcept_executeAddi colour excluded valid
        injective colourZero source target hrelation hzeroSource hzeroTarget
        hname sourceName hsource hsourceNe value
  | sub =>
      simpa using wordColourStateRelationExcept_executeAddi colour excluded valid
        injective colourZero source target hrelation hzeroSource hzeroTarget
        hname sourceName hsource hsourceNe (0 - value)
  | and =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ &&& value =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ &&& value := by
        rw [hrelation.register sourceName hsource hsourceNe (valid sourceName hsource)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname (readRegister source ⟨sourceName, hsource⟩ &&& value)
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ &&& value) hvalue)
  | or =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ ||| value =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ||| value := by
        rw [hrelation.register sourceName hsource hsourceNe (valid sourceName hsource)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname (readRegister source ⟨sourceName, hsource⟩ ||| value)
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ||| value) hvalue)
  | xor =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ ^^^ value =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ^^^ value := by
        rw [hrelation.register sourceName hsource hsourceNe (valid sourceName hsource)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname (readRegister source ⟨sourceName, hsource⟩ ^^^ value)
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ^^^ value) hvalue)

theorem wordColourStateRelationExcept_executeShiftImmediate
    [NeZero width]
    (colour : Nat → Nat) (excluded : Nat)
    (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept colour excluded source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (operator : Shift) (sourceName : Nat) (amount : Word width)
    (hoperator : operator ≠ .ror) (hname : excluded < 32)
    (hsource : sourceName < 32) (hsourceNe : sourceName ≠ excluded) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .lsl => .slli ⟨excluded, hname⟩ ⟨sourceName, hsource⟩ amount
        | .lsr => .srli ⟨excluded, hname⟩ ⟨sourceName, hsource⟩ amount
        | .asr => .srai ⟨excluded, hname⟩ ⟨sourceName, hsource⟩ amount
        | .ror => .slli ⟨excluded, hname⟩ ⟨sourceName, hsource⟩ amount))
      (execute target (match operator with
        | .lsl => .slli ⟨colour excluded, valid excluded hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ amount
        | .lsr => .srli ⟨colour excluded, valid excluded hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ amount
        | .asr => .srai ⟨colour excluded, valid excluded hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ amount
        | .ror => .slli ⟨colour excluded, valid excluded hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ amount)) := by
  cases operator with
  | lsl =>
      have hvalue :
          BitVec.shiftLeft (readRegister source ⟨sourceName, hsource⟩)
              (shiftAmount amount) =
            BitVec.shiftLeft (readRegister target
              ⟨colour sourceName, valid sourceName hsource⟩) (shiftAmount amount) := by
        rw [hrelation.register sourceName hsource hsourceNe (valid sourceName hsource)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname
          (BitVec.shiftLeft (readRegister source ⟨sourceName, hsource⟩)
            (shiftAmount amount))
          (BitVec.shiftLeft (readRegister target
            ⟨colour sourceName, valid sourceName hsource⟩) (shiftAmount amount)) hvalue)
  | lsr =>
      have hvalue :
          BitVec.ushiftRight (readRegister source ⟨sourceName, hsource⟩)
              (shiftAmount amount) =
            BitVec.ushiftRight (readRegister target
              ⟨colour sourceName, valid sourceName hsource⟩) (shiftAmount amount) := by
        rw [hrelation.register sourceName hsource hsourceNe (valid sourceName hsource)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname
          (BitVec.ushiftRight (readRegister source ⟨sourceName, hsource⟩)
            (shiftAmount amount))
          (BitVec.ushiftRight (readRegister target
            ⟨colour sourceName, valid sourceName hsource⟩) (shiftAmount amount)) hvalue)
  | asr =>
      have hvalue :
          BitVec.sshiftRight (readRegister source ⟨sourceName, hsource⟩)
              (shiftAmount amount) =
            BitVec.sshiftRight (readRegister target
              ⟨colour sourceName, valid sourceName hsource⟩) (shiftAmount amount) := by
        rw [hrelation.register sourceName hsource hsourceNe (valid sourceName hsource)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname
          (BitVec.sshiftRight (readRegister source ⟨sourceName, hsource⟩)
            (shiftAmount amount))
          (BitVec.sshiftRight (readRegister target
            ⟨colour sourceName, valid sourceName hsource⟩) (shiftAmount amount)) hvalue)
  | ror => exact (hoperator rfl).elim

theorem wordColourStateRelationExcept_executeShift
    [NeZero width]
    (colour : Nat → Nat) (excluded : Nat)
    (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept colour excluded source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (operator : Shift) (left right : Nat) (hoperator : operator ≠ .ror)
    (hname : excluded < 32) (hleft : left < 32) (hright : right < 32)
    (hleftNe : left ≠ excluded) (hrightNe : right ≠ excluded) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .lsl => .sll ⟨excluded, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .lsr => .srl ⟨excluded, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .asr => .sra ⟨excluded, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .ror => .sll ⟨excluded, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
      (execute target (match operator with
        | .lsl => .sll ⟨colour excluded, valid excluded hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .lsr => .srl ⟨colour excluded, valid excluded hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .asr => .sra ⟨colour excluded, valid excluded hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .ror => .sll ⟨colour excluded, valid excluded hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
  cases operator with
  | lsl =>
      have hvalue :
          BitVec.shiftLeft (readRegister source ⟨left, hleft⟩)
              (shiftAmount (readRegister source ⟨right, hright⟩)) =
            BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount (readRegister target ⟨colour right, valid right hright⟩)) := by
        rw [hrelation.register left hleft hleftNe (valid left hleft),
          hrelation.register right hright hrightNe (valid right hright)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname
          (BitVec.shiftLeft (readRegister source ⟨left, hleft⟩)
            (shiftAmount (readRegister source ⟨right, hright⟩)))
          (BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount (readRegister target ⟨colour right, valid right hright⟩))) hvalue)
  | lsr =>
      have hvalue :
          BitVec.ushiftRight (readRegister source ⟨left, hleft⟩)
              (shiftAmount (readRegister source ⟨right, hright⟩)) =
            BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount (readRegister target ⟨colour right, valid right hright⟩)) := by
        rw [hrelation.register left hleft hleftNe (valid left hleft),
          hrelation.register right hright hrightNe (valid right hright)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname
          (BitVec.ushiftRight (readRegister source ⟨left, hleft⟩)
            (shiftAmount (readRegister source ⟨right, hright⟩)))
          (BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount (readRegister target ⟨colour right, valid right hright⟩))) hvalue)
  | asr =>
      have hvalue :
          BitVec.sshiftRight (readRegister source ⟨left, hleft⟩)
              (shiftAmount (readRegister source ⟨right, hright⟩)) =
            BitVec.sshiftRight (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount (readRegister target ⟨colour right, valid right hright⟩)) := by
        rw [hrelation.register left hleft hleftNe (valid left hleft),
          hrelation.register right hright hrightNe (valid right hright)]
      have hnext := wordColourStateRelationExcept_nextPc colour excluded source target hrelation
      simpa [execute] using
        (wordColourStateRelationExcept_writeRegister colour excluded valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target} hnext
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroSource)
          (by simpa [ZeroRegister, readRegister, nextPc] using hzeroTarget)
          hname
          (BitVec.sshiftRight (readRegister source ⟨left, hleft⟩)
            (shiftAmount (readRegister source ⟨right, hright⟩)))
          (BitVec.sshiftRight (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount (readRegister target ⟨colour right, valid right hright⟩))) hvalue)
  | ror => exact (hoperator rfl).elim

theorem ssaRenameAssign_eq_applyColour
    [NeZero width] (ssa : WordSsaState) (name : Nat)
    (value : WordExp (Word width))
    (hprogram : WordVarStraightLine width (.assign name value))
    (hnot : name ∉ wordExpReadVars value) :
    (wordSsaRenameProgram ssa (.assign name value)).2 =
      wordApplyColour (ssaAssignmentColour ssa name)
        (.assign name value) := by
  cases hprogram with
  | assign name source hname hsource =>
      have hne : name ≠ source := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hne' : source ≠ name := Ne.symm hne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hne']
  | assignConst name value hname =>
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp]
  | assignBinary operator name left right hname hleft hright =>
      have hleft_ne : name ≠ left := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hright_ne : name ≠ right := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hleft_ne' : left ≠ name := Ne.symm hleft_ne
      have hright_ne' : right ≠ name := Ne.symm hright_ne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hleft_ne', hright_ne']
  | assignImmediate operator name source value hname hsource =>
      have hne : name ≠ source := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hne' : source ≠ name := Ne.symm hne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hne']
  | assignShift operator name left right hoperator hname hleft hright =>
      have hleft_ne : name ≠ left := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hright_ne : name ≠ right := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hleft_ne' : left ≠ name := Ne.symm hleft_ne
      have hright_ne' : right ≠ name := Ne.symm hright_ne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hleft_ne', hright_ne']
  | assignShiftImmediate operator name left amount hoperator hname hleft =>
      have hne : name ≠ left := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hne' : left ≠ name := Ne.symm hne
      simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
        ssaAssignmentColour, wordSsaFresh, wordSsaRenameExp,
        wordApplyColour, wordApplyColourExp, hne']

/-! The first SSA assignment simulation permits an arbitrary old value in the
    fresh target register.  This is the overwrite property needed before
    composing multiple SSA writes. -/

theorem evalWordFunction_ssaRenameAssignConst_applyColourExcept
    [NeZero width]
    (ssa : WordSsaState) (name : Nat) (value : Word width)
    (valid : wordColourValid (ssaAssignmentColour ssa name))
    (injective : Function.Injective (ssaAssignmentColour ssa name))
    (colourZero : ssaAssignmentColour ssa name 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept
      (ssaAssignmentColour ssa name) name source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hname : name < 32) :
    ∃ source' target',
      evalWordFunction source (.assign name (.const value)) =
        some (source', []) ∧
      evalWordFunction target
          (wordSsaRenameProgram ssa (.assign name (.const value))).2 =
        some (target', []) ∧
      WordColourStateRelation (ssaAssignmentColour ssa name) source' target' := by
  let colour := ssaAssignmentColour ssa name
  have hprogram : WordVarStraightLine width
      (.assign name (.const value)) :=
    .assignConst name value hname
  have hnot : name ∉ wordExpReadVars (.const value) := by
    simp [wordExpReadVars]
  have hrename := ssaRenameAssign_eq_applyColour ssa name (.const value)
    hprogram hnot
  have hsourceEval :
      evalWordFunction source (.assign name (.const value)) =
        some (execute source (.addi ⟨name, hname⟩ 0 value), []) := by
    simp [evalWordFunction, wordExpToInstructions,
      wordExpToInstruction, registerOfNat, hname, executeInstructions]
  have htargetEval :
      evalWordFunction target
          (wordSsaRenameProgram ssa (.assign name (.const value))).2 =
        some (execute target
          (.addi ⟨colour name, valid name hname⟩ 0 value), []) := by
    rw [hrename]
    simp [colour, evalWordFunction, wordApplyColour,
      wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, valid name hname, executeInstructions]
  have hrelation' := wordColourStateRelationExcept_executeConst
    colour name valid injective colourZero source target hrelation
    hzeroSource hzeroTarget hname value
  exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩

theorem evalWordFunction_ssaRenameAssignVar_applyColourExcept
    [NeZero width]
    (ssa : WordSsaState) (name sourceName : Nat)
    (valid : wordColourValid (ssaAssignmentColour ssa name))
    (injective : Function.Injective (ssaAssignmentColour ssa name))
    (colourZero : ssaAssignmentColour ssa name 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept
      (ssaAssignmentColour ssa name) name source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hname : name < 32) (hsource : sourceName < 32)
    (hsourceNe : sourceName ≠ name) :
    ∃ source' target',
      evalWordFunction source (.assign name (.var sourceName)) =
        some (source', []) ∧
      evalWordFunction target
          (wordSsaRenameProgram ssa (.assign name (.var sourceName))).2 =
        some (target', []) ∧
      WordColourStateRelation (ssaAssignmentColour ssa name) source' target' := by
  let colour := ssaAssignmentColour ssa name
  have hprogram : WordVarStraightLine width
      (.assign name (.var sourceName)) :=
    .assign name sourceName hname hsource
  have hnot : name ∉ wordExpReadVars
      (.var sourceName : WordExp (Word width)) := by
    simpa [wordExpReadVars] using (Ne.symm hsourceNe)
  have hrename := ssaRenameAssign_eq_applyColour ssa name (.var sourceName)
    hprogram hnot
  have hsourceEval :
      evalWordFunction source (.assign name (.var sourceName)) =
        some (execute source
          (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ 0), []) := by
    simp [evalWordFunction, wordExpToInstructions,
      wordExpToInstruction, registerOfNat, hname, hsource,
      executeInstructions]
  have htargetEval :
      evalWordFunction target
          (wordSsaRenameProgram ssa (.assign name (.var sourceName))).2 =
        some (execute target
          (.addi ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ 0), []) := by
    rw [hrename]
    simp [colour, evalWordFunction, wordApplyColour,
      wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, valid name hname, valid sourceName hsource,
      executeInstructions]
  have hrelation' := wordColourStateRelationExcept_executeAddi
    colour name valid injective colourZero source target hrelation
    hzeroSource hzeroTarget hname sourceName hsource hsourceNe 0
  exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩

theorem evalWordFunction_ssaRenameAssignBinary_applyColourExcept
    [NeZero width]
    (ssa : WordSsaState) (operator : BinOp) (name left right : Nat)
    (valid : wordColourValid (ssaAssignmentColour ssa name))
    (injective : Function.Injective (ssaAssignmentColour ssa name))
    (colourZero : ssaAssignmentColour ssa name 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept
      (ssaAssignmentColour ssa name) name source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hname : name < 32) (hleft : left < 32) (hright : right < 32)
    (hleftNe : left ≠ name) (hrightNe : right ≠ name) :
    ∃ source' target',
      evalWordFunction source
          (.assign name (.op operator [.var left, .var right])) =
        some (source', []) ∧
      evalWordFunction target
          (wordSsaRenameProgram ssa
            (.assign name (.op operator [.var left, .var right]))).2 =
        some (target', []) ∧
      WordColourStateRelation (ssaAssignmentColour ssa name) source' target' := by
  let colour := ssaAssignmentColour ssa name
  have hprogram : WordVarStraightLine width
      (.assign name (.op operator [.var left, .var right])) :=
    .assignBinary operator name left right hname hleft hright
  have hnot : name ∉ wordExpReadVars
      (.op operator [.var left, .var right] : WordExp (Word width)) := by
    simp [wordExpReadVars, Ne.symm hleftNe, Ne.symm hrightNe]
  have hrename := ssaRenameAssign_eq_applyColour ssa name
    (.op operator [.var left, .var right]) hprogram hnot
  cases operator with
  | add =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.op .add [.var left, .var right])) =
            some (execute source
              (.add ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.op .add [.var left, .var right]))).2 =
            some (execute target
              (.add ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩
                ⟨colour right, valid right hright⟩), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeBinary
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .add left right hname hleft hright
        hleftNe hrightNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | sub =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.op .sub [.var left, .var right])) =
            some (execute source
              (.sub ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.op .sub [.var left, .var right]))).2 =
            some (execute target
              (.sub ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩
                ⟨colour right, valid right hright⟩), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeBinary
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .sub left right hname hleft hright
        hleftNe hrightNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | and =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.op .and [.var left, .var right])) =
            some (execute source
              (.and ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.op .and [.var left, .var right]))).2 =
            some (execute target
              (.and ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩
                ⟨colour right, valid right hright⟩), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeBinary
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .and left right hname hleft hright
        hleftNe hrightNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | or =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.op .or [.var left, .var right])) =
            some (execute source
              (.or ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.op .or [.var left, .var right]))).2 =
            some (execute target
              (.or ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩
                ⟨colour right, valid right hright⟩), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeBinary
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .or left right hname hleft hright
        hleftNe hrightNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | xor =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.op .xor [.var left, .var right])) =
            some (execute source
              (.xor ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.op .xor [.var left, .var right]))).2 =
            some (execute target
              (.xor ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩
                ⟨colour right, valid right hright⟩), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeBinary
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .xor left right hname hleft hright
        hleftNe hrightNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩

theorem evalWordFunction_ssaRenameAssignImmediate_applyColourExcept
    [NeZero width]
    (ssa : WordSsaState) (operator : BinOp) (name sourceName : Nat)
    (value : Word width)
    (valid : wordColourValid (ssaAssignmentColour ssa name))
    (injective : Function.Injective (ssaAssignmentColour ssa name))
    (colourZero : ssaAssignmentColour ssa name 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept
      (ssaAssignmentColour ssa name) name source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hname : name < 32) (hsource : sourceName < 32)
    (hsourceNe : sourceName ≠ name) :
    ∃ source' target',
      evalWordFunction source
          (.assign name (.op operator [.var sourceName, .const value])) =
        some (source', []) ∧
      evalWordFunction target
          (wordSsaRenameProgram ssa
            (.assign name (.op operator [.var sourceName, .const value]))).2 =
        some (target', []) ∧
      WordColourStateRelation (ssaAssignmentColour ssa name) source' target' := by
  let colour := ssaAssignmentColour ssa name
  have hprogram : WordVarStraightLine width
      (.assign name (.op operator [.var sourceName, .const value])) :=
    .assignImmediate operator name sourceName value hname hsource
  have hnot : name ∉ wordExpReadVars
      (.op operator [.var sourceName, .const value] : WordExp (Word width)) := by
    simp [wordExpReadVars, Ne.symm hsourceNe]
  have hrename := ssaRenameAssign_eq_applyColour ssa name
    (.op operator [.var sourceName, .const value]) hprogram hnot
  cases operator with
  | add =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.op .add [.var sourceName, .const value])) =
            some (execute source
              (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ value), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.op .add [.var sourceName, .const value]))).2 =
            some (execute target
              (.addi ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid sourceName hsource,
          executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeImmediateBinary
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .add sourceName value hname hsource hsourceNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | sub =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.op .sub [.var sourceName, .const value])) =
            some (execute source
              (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ (0 - value)), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.op .sub [.var sourceName, .const value]))).2 =
            some (execute target
              (.addi ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ (0 - value)), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid sourceName hsource,
          executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeImmediateBinary
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .sub sourceName value hname hsource hsourceNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | and =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.op .and [.var sourceName, .const value])) =
            some (execute source
              (.andi ⟨name, hname⟩ ⟨sourceName, hsource⟩ value), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.op .and [.var sourceName, .const value]))).2 =
            some (execute target
              (.andi ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid sourceName hsource,
          executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeImmediateBinary
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .and sourceName value hname hsource hsourceNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | or =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.op .or [.var sourceName, .const value])) =
            some (execute source
              (.ori ⟨name, hname⟩ ⟨sourceName, hsource⟩ value), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.op .or [.var sourceName, .const value]))).2 =
            some (execute target
              (.ori ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid sourceName hsource,
          executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeImmediateBinary
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .or sourceName value hname hsource hsourceNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | xor =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.op .xor [.var sourceName, .const value])) =
            some (execute source
              (.xori ⟨name, hname⟩ ⟨sourceName, hsource⟩ value), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.op .xor [.var sourceName, .const value]))).2 =
            some (execute target
              (.xori ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid sourceName hsource,
          executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeImmediateBinary
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .xor sourceName value hname hsource hsourceNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩

theorem evalWordFunction_ssaRenameAssignShiftImmediate_applyColourExcept
    [NeZero width]
    (ssa : WordSsaState) (operator : Shift) (name left : Nat)
    (amount : Word width)
    (valid : wordColourValid (ssaAssignmentColour ssa name))
    (injective : Function.Injective (ssaAssignmentColour ssa name))
    (colourZero : ssaAssignmentColour ssa name 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept
      (ssaAssignmentColour ssa name) name source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hoperator : operator ≠ .ror) (hname : name < 32) (hleft : left < 32)
    (hleftNe : left ≠ name) :
    ∃ source' target',
      evalWordFunction source
          (.assign name (.shift operator (.var left) (.const amount))) =
        some (source', []) ∧
      evalWordFunction target
          (wordSsaRenameProgram ssa
            (.assign name (.shift operator (.var left) (.const amount)))).2 =
        some (target', []) ∧
      WordColourStateRelation (ssaAssignmentColour ssa name) source' target' := by
  let colour := ssaAssignmentColour ssa name
  have hprogram : WordVarStraightLine width
      (.assign name (.shift operator (.var left) (.const amount))) :=
    .assignShiftImmediate operator name left amount hoperator hname hleft
  have hnot : name ∉ wordExpReadVars
      (.shift operator (.var left) (.const amount) : WordExp (Word width)) := by
    simp [wordExpReadVars, Ne.symm hleftNe]
  have hrename := ssaRenameAssign_eq_applyColour ssa name
    (.shift operator (.var left) (.const amount)) hprogram hnot
  cases operator with
  | lsl =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.shift .lsl (.var left) (.const amount))) =
            some (execute source (.slli ⟨name, hname⟩ ⟨left, hleft⟩ amount), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.shift .lsl (.var left) (.const amount)))).2 =
            some (execute target
              (.slli ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ amount), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid left hleft,
          executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeShiftImmediate
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .lsl left amount hoperator hname hleft hleftNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | lsr =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.shift .lsr (.var left) (.const amount))) =
            some (execute source (.srli ⟨name, hname⟩ ⟨left, hleft⟩ amount), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.shift .lsr (.var left) (.const amount)))).2 =
            some (execute target
              (.srli ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ amount), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid left hleft,
          executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeShiftImmediate
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .lsr left amount hoperator hname hleft hleftNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | asr =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.shift .asr (.var left) (.const amount))) =
            some (execute source (.srai ⟨name, hname⟩ ⟨left, hleft⟩ amount), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.shift .asr (.var left) (.const amount)))).2 =
            some (execute target
              (.srai ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ amount), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid left hleft,
          executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeShiftImmediate
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .asr left amount hoperator hname hleft hleftNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | ror => exact (hoperator rfl).elim

theorem evalWordFunction_ssaRenameAssignShift_applyColourExcept
    [NeZero width]
    (ssa : WordSsaState) (operator : Shift) (name left right : Nat)
    (valid : wordColourValid (ssaAssignmentColour ssa name))
    (injective : Function.Injective (ssaAssignmentColour ssa name))
    (colourZero : ssaAssignmentColour ssa name 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept
      (ssaAssignmentColour ssa name) name source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hoperator : operator ≠ .ror) (hname : name < 32) (hleft : left < 32)
    (hright : right < 32) (hleftNe : left ≠ name) (hrightNe : right ≠ name) :
    ∃ source' target',
      evalWordFunction source
          (.assign name (.shift operator (.var left) (.var right))) =
        some (source', []) ∧
      evalWordFunction target
          (wordSsaRenameProgram ssa
            (.assign name (.shift operator (.var left) (.var right)))).2 =
        some (target', []) ∧
      WordColourStateRelation (ssaAssignmentColour ssa name) source' target' := by
  let colour := ssaAssignmentColour ssa name
  have hprogram : WordVarStraightLine width
      (.assign name (.shift operator (.var left) (.var right))) :=
    .assignShift operator name left right hoperator hname hleft hright
  have hnot : name ∉ wordExpReadVars
      (.shift operator (.var left) (.var right) : WordExp (Word width)) := by
    simp [wordExpReadVars, Ne.symm hleftNe, Ne.symm hrightNe]
  have hrename := ssaRenameAssign_eq_applyColour ssa name
    (.shift operator (.var left) (.var right)) hprogram hnot
  cases operator with
  | lsl =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.shift .lsl (.var left) (.var right))) =
            some (execute source
              (.sll ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.shift .lsl (.var left) (.var right)))).2 =
            some (execute target
              (.sll ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩
                ⟨colour right, valid right hright⟩), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeShift
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .lsl left right hoperator hname hleft hright
        hleftNe hrightNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | lsr =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.shift .lsr (.var left) (.var right))) =
            some (execute source
              (.srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.shift .lsr (.var left) (.var right)))).2 =
            some (execute target
              (.srl ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩
                ⟨colour right, valid right hright⟩), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeShift
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .lsr left right hoperator hname hleft hright
        hleftNe hrightNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | asr =>
      have hsourceEval :
          evalWordFunction source
              (.assign name (.shift .asr (.var left) (.var right))) =
            some (execute source
              (.sra ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩), []) := by
        simp [evalWordFunction, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordFunction target
              (wordSsaRenameProgram ssa
                (.assign name (.shift .asr (.var left) (.var right)))).2 =
            some (execute target
              (.sra ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩
                ⟨colour right, valid right hright⟩), []) := by
        rw [hrename]
        simp [colour, evalWordFunction, wordApplyColour,
          wordApplyColourExp, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      have hrelation' := wordColourStateRelationExcept_executeShift
        colour name valid injective colourZero source target hrelation
        hzeroSource hzeroTarget .asr left right hoperator hname hleft hright
        hleftNe hrightNe
      exact ⟨_, _, hsourceEval, htargetEval, hrelation'⟩
  | ror => exact (hoperator rfl).elim

theorem evalWordFunction_ssaRenameAssignExcept
    [NeZero width]
    (ssa : WordSsaState) (name : Nat) (value : WordExp (Word width))
    (valid : wordColourValid (ssaAssignmentColour ssa name))
    (injective : Function.Injective (ssaAssignmentColour ssa name))
    (colourZero : ssaAssignmentColour ssa name 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelationExcept
      (ssaAssignmentColour ssa name) name source target)
    (hzeroSource : ZeroRegister source) (hzeroTarget : ZeroRegister target)
    (hprogram : WordVarStraightLine width (.assign name value))
    (hnot : name ∉ wordExpReadVars value) :
    ∃ source' target',
      evalWordFunction source (.assign name value) = some (source', []) ∧
      evalWordFunction target
          (wordSsaRenameProgram ssa (.assign name value)).2 =
        some (target', []) ∧
      WordColourStateRelation (ssaAssignmentColour ssa name) source' target' := by
  cases hprogram with
  | assign name sourceName hname hsource =>
      have hsourceNe : sourceName ≠ name := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      exact evalWordFunction_ssaRenameAssignVar_applyColourExcept
        ssa name sourceName valid injective colourZero source target hrelation
        hzeroSource hzeroTarget hname hsource hsourceNe
  | assignConst name value hname =>
      exact evalWordFunction_ssaRenameAssignConst_applyColourExcept
        ssa name value valid injective colourZero source target hrelation
        hzeroSource hzeroTarget hname
  | assignBinary operator name left right hname hleft hright =>
      have hleftNe : left ≠ name := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hrightNe : right ≠ name := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      exact evalWordFunction_ssaRenameAssignBinary_applyColourExcept
        ssa operator name left right valid injective colourZero source target
        hrelation hzeroSource hzeroTarget hname hleft hright hleftNe hrightNe
  | assignImmediate operator name sourceName value hname hsource =>
      have hsourceNe : sourceName ≠ name := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      exact evalWordFunction_ssaRenameAssignImmediate_applyColourExcept
        ssa operator name sourceName value valid injective colourZero source target
        hrelation hzeroSource hzeroTarget hname hsource hsourceNe
  | assignShift operator name left right hoperator hname hleft hright =>
      have hleftNe : left ≠ name := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      have hrightNe : right ≠ name := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      exact evalWordFunction_ssaRenameAssignShift_applyColourExcept
        ssa operator name left right valid injective colourZero source target
        hrelation hzeroSource hzeroTarget hoperator hname hleft hright
        hleftNe hrightNe
  | assignShiftImmediate operator name left amount hoperator hname hleft =>
      have hleftNe : left ≠ name := by
        intro heq
        apply hnot
        simp [wordExpReadVars, heq]
      exact evalWordFunction_ssaRenameAssignShiftImmediate_applyColourExcept
        ssa operator name left amount valid injective colourZero source target
        hrelation hzeroSource hzeroTarget hoperator hname hleft hleftNe

theorem evalWordFunction_ssaRenameAssign_applyColour
    [NeZero width]
    (ssa : WordSsaState) (name : Nat) (value : WordExp (Word width))
    (valid : wordColourValid (ssaAssignmentColour ssa name))
    (injective : Function.Injective (ssaAssignmentColour ssa name))
    (colourZero : ssaAssignmentColour ssa name 0 = 0)
    (colourNoScratch : ∀ current, current < 31 →
      ssaAssignmentColour ssa name current ≠ 31)
    (source target : State width)
    (hrelation : WordColourStateRelation
      (ssaAssignmentColour ssa name) source target)
    (hprogram : WordVarStraightLine width (.assign name value))
    (hnot : name ∉ wordExpReadVars value) :
    ∃ source' target',
      evalWordFunction source (.assign name value) = some (source', []) ∧
      evalWordFunction target
          (wordSsaRenameProgram ssa (.assign name value)).2 =
        some (target', []) ∧
      WordColourStateRelation (ssaAssignmentColour ssa name) source' target' := by
  rcases evalWordFunction_wordVarStraightLine_applyColour
    (ssaAssignmentColour ssa name) valid injective colourZero colourNoScratch
    source target hrelation (.assign name value) hprogram with
    ⟨source', target', hsource, htarget, hrelation'⟩
  have hrename := ssaRenameAssign_eq_applyColour ssa name value hprogram hnot
  refine ⟨source', target', hsource, ?_, hrelation'⟩
  simpa [hrename] using htarget

end Flapjack.RiscV
