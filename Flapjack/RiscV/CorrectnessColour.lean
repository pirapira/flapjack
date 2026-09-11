import Flapjack.RiscV.AllocatorCorrectness
import Flapjack.RiscV.CorrectnessBackend
import Flapjack.RiscV.CorrectnessFfi

/-!
Correctness of applying a register colouring to a small, executable Word
fragment. This is the first whole-program simulation statement for allocator
output: it covers straight-line programs made from `skip`, variable-to-
variable assignments, and sequencing.
-/

namespace Flapjack.RiscV

def wordColourValid (colour : Nat → Nat) : Prop :=
  ∀ name, name < 32 → colour name < 32

structure WordColourStateRelation (colour : Nat → Nat) [NeZero width]
    (source target : State width) : Prop where
  pc : source.pc = target.pc
  memory : source.memory = target.memory
  privilege : source.privilege = target.privilege
  mode : source.mode = target.mode
  register : ∀ (name : Nat) (hname : name < 32)
      (hcolour : colour name < 32),
    readRegister source ⟨name, hname⟩ =
      readRegister target ⟨colour name, hcolour⟩

theorem wordColourStateRelation_nextPc
    (colour : Nat → Nat) (_valid : wordColourValid colour)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target) :
    WordColourStateRelation colour
      {source with pc := nextPc source} {target with pc := nextPc target} := by
  constructor
  · simp [nextPc, hrelation.pc]
  · exact hrelation.memory
  · exact hrelation.privilege
  · exact hrelation.mode
  · intro name hname hcolour
    exact hrelation.register name hname hcolour

theorem wordColourStateRelation_writeRegister
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name : Nat) (hname : name < 32) (value targetValue : Word width)
    (hvalue : value = targetValue) :
    WordColourStateRelation colour
      (writeRegister source ⟨name, hname⟩ value)
      (writeRegister target ⟨colour name, valid name hname⟩ targetValue) := by
  by_cases hzero : name = 0
  · have hcolourZero : colour name = 0 := by simpa [hzero] using colourZero
    simpa [writeRegister, hzero, hcolourZero, colourZero] using hrelation
  have hsourceNonzero : (⟨name, hname⟩ : Fin 32) ≠ 0 := by
    intro h
    exact hzero (congrArg Fin.val h)
  have hcolourNonzero : colour name ≠ 0 := by
    intro h
    apply hzero
    apply injective
    simpa [colourZero] using h
  have htargetNonzero :
      (⟨colour name, valid name hname⟩ : Fin 32) ≠ 0 := by
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
    by_cases hsame : current = name
    · subst current
      have hsourceEq :
          (⟨name, hcurrent⟩ : Fin 32) = ⟨name, hname⟩ := by
        apply Fin.ext
        rfl
      have htargetEq :
          (⟨colour name, hcolour⟩ : Fin 32) =
            ⟨colour name, valid name hname⟩ := by
        apply Fin.ext
        rfl
      simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false,
        readRegister]
      simp only [if_true]
      exact hvalue
    · have htargetSame :
          (⟨colour current, hcolour⟩ : Fin 32) ≠
            (⟨colour name, valid name hname⟩ : Fin 32) := by
          intro h
          apply hsame
          apply injective
          exact congrArg Fin.val h
      have hsourceCurrent :
          (⟨current, hcurrent⟩ : Fin 32) ≠ ⟨name, hname⟩ := by
        intro h
        apply hsame
        exact congrArg Fin.val h
      simp only [writeRegister, hsourceNonzero, htargetNonzero, if_false,
        readRegister]
      rw [if_neg hsourceCurrent, if_neg htargetSame]
      exact hrelation.register current hcurrent hcolour

theorem wordColourStateRelation_executeAddi
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name sourceName : Nat) (hname : name < 32)
    (hsource : sourceName < 32) :
    WordColourStateRelation colour
      (execute source (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ 0))
      (execute target
        (.addi ⟨colour name, valid name hname⟩
          ⟨colour sourceName, valid sourceName hsource⟩ 0)) := by
  have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
  have hvalue :
      readRegister source ⟨sourceName, hsource⟩ + 0 =
        readRegister target ⟨colour sourceName, valid sourceName hsource⟩ + 0 := by
    rw [hrelation.register sourceName hsource (valid sourceName hsource)]
  simpa [execute] using
    (wordColourStateRelation_writeRegister colour valid injective colourZero
      {source with pc := nextPc source} {target with pc := nextPc target}
      hnext name hname
      (readRegister source ⟨sourceName, hsource⟩ + 0)
      (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ + 0)
      hvalue)

theorem evalWordProg_assignVar_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name sourceName : Nat) (hname : name < 32) (hsource : sourceName < 32) :
    ∃ source' target',
      evalWordProg source (.assign name (.var sourceName)) = some source' ∧
      evalWordProg target
          (wordApplyColour colour (.assign name (.var sourceName))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  have hsourceEval :
      evalWordProg source (.assign name (.var sourceName)) =
        some (execute source (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ 0)) := by
    simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, hname, hsource, executeInstructions]
  have htargetEval :
      evalWordProg target
          (wordApplyColour colour (.assign name (.var sourceName))) =
        some (execute target
          (.addi ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ 0)) := by
    rw [wordApplyColour_assign]
    simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, valid name hname, valid sourceName hsource,
      executeInstructions]
  exact ⟨_, _, hsourceEval, htargetEval,
      wordColourStateRelation_executeAddi colour valid injective colourZero
      source target hrelation name sourceName hname hsource⟩

theorem evalWordProg_assignConst_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name : Nat) (value : Word width) (hname : name < 32) :
    ∃ source' target',
      evalWordProg source (.assign name (.const value)) = some source' ∧
      evalWordProg target
          (wordApplyColour colour (.assign name (.const value))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
  have hread : readRegister source 0 = readRegister target 0 := by
    simpa [colourZero] using
      hrelation.register 0 (by omega) (by simp [colourZero])
  have hvalue :
      readRegister source 0 + value = readRegister target 0 + value := by
    rw [hread]
  have hsourceEval :
      evalWordProg source (.assign name (.const value)) =
        some (execute source (.addi ⟨name, hname⟩ 0 value)) := by
    simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
      registerOfNat, hname, executeInstructions]
  have htargetEval :
      evalWordProg target
          (wordApplyColour colour (.assign name (.const value))) =
        some (execute target
          (.addi ⟨colour name, valid name hname⟩ 0 value)) := by
    simp [wordApplyColour, wordApplyColourExp, evalWordProg,
      wordExpToInstructions, wordExpToInstruction, registerOfNat,
      valid name hname, executeInstructions]
  have hstate := wordColourStateRelation_writeRegister colour valid
    injective colourZero {source with pc := nextPc source}
    {target with pc := nextPc target} hnext name hname
    (readRegister source 0 + value) (readRegister target 0 + value) hvalue
  exact ⟨_, _, hsourceEval, htargetEval, by
    simpa [execute, colourZero] using hstate⟩

theorem wordColourStateRelation_executeBinary
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : BinOp) (name left right : Nat)
    (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .add => .add ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .sub => .sub ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .and => .and ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .or => .or ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .xor => .xor ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
      (execute target (match operator with
        | .add => .add ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .sub => .sub ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .and => .and ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .or => .or ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .xor => .xor ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
  cases operator with
  | add =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ + readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ +
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨left, hleft⟩ + readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ +
            readRegister target ⟨colour right, valid right hright⟩) hvalue)
  | sub =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ - readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ -
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨left, hleft⟩ - readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ -
            readRegister target ⟨colour right, valid right hright⟩) hvalue)
  | and =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ &&& readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ &&&
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨left, hleft⟩ &&& readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ &&&
            readRegister target ⟨colour right, valid right hright⟩) hvalue)
  | or =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ ||| readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ |||
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨left, hleft⟩ ||| readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ |||
            readRegister target ⟨colour right, valid right hright⟩) hvalue)
  | xor =>
      have hvalue :
          readRegister source ⟨left, hleft⟩ ^^^ readRegister source ⟨right, hright⟩ =
            readRegister target ⟨colour left, valid left hleft⟩ ^^^
              readRegister target ⟨colour right, valid right hright⟩ := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨left, hleft⟩ ^^^ readRegister source ⟨right, hright⟩)
          (readRegister target ⟨colour left, valid left hleft⟩ ^^^
            readRegister target ⟨colour right, valid right hright⟩) hvalue)

theorem evalWordProg_assignBinaryVarVar_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : BinOp) (name left right : Nat)
    (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
    ∃ source' target',
      evalWordProg source
          (.assign name (.op operator [.var left, .var right])) = some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.op operator [.var left, .var right]))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  cases operator with
  | add =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .add [.var left, .var right])) =
            some (execute source (.add ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .add [.var left, .var right]))) =
            some (execute target
              (.add ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeBinary colour valid injective colourZero
          source target hrelation .add name left right hname hleft hright⟩
  | sub =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .sub [.var left, .var right])) =
            some (execute source (.sub ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .sub [.var left, .var right]))) =
            some (execute target
              (.sub ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeBinary colour valid injective colourZero
          source target hrelation .sub name left right hname hleft hright⟩
  | and =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .and [.var left, .var right])) =
            some (execute source (.and ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .and [.var left, .var right]))) =
            some (execute target
              (.and ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeBinary colour valid injective colourZero
          source target hrelation .and name left right hname hleft hright⟩
  | or =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .or [.var left, .var right])) =
            some (execute source (.or ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .or [.var left, .var right]))) =
            some (execute target
              (.or ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeBinary colour valid injective colourZero
          source target hrelation .or name left right hname hleft hright⟩
  | xor =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .xor [.var left, .var right])) =
            some (execute source (.xor ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .xor [.var left, .var right]))) =
            some (execute target
              (.xor ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeBinary colour valid injective colourZero
          source target hrelation .xor name left right hname hleft hright⟩

theorem wordColourStateRelation_executeImmediateBinary
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : BinOp) (name sourceName : Nat) (value : Word width)
    (hname : name < 32) (hsource : sourceName < 32) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .add => .addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ value
        | .sub => .addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ (0 - value)
        | .and => .andi ⟨name, hname⟩ ⟨sourceName, hsource⟩ value
        | .or => .ori ⟨name, hname⟩ ⟨sourceName, hsource⟩ value
        | .xor => .xori ⟨name, hname⟩ ⟨sourceName, hsource⟩ value))
      (execute target (match operator with
        | .add => .addi ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value
        | .sub => .addi ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ (0 - value)
        | .and => .andi ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value
        | .or => .ori ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value
        | .xor => .xori ⟨colour name, valid name hname⟩
            ⟨colour sourceName, valid sourceName hsource⟩ value)) := by
  cases operator with
  | add =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ + value =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ + value := by
        rw [hrelation.register sourceName hsource (valid sourceName hsource)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨sourceName, hsource⟩ + value)
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ + value) hvalue)
  | sub =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ + (0 - value) =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ +
              (0 - value) := by
        rw [hrelation.register sourceName hsource (valid sourceName hsource)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨sourceName, hsource⟩ + (0 - value))
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ +
            (0 - value)) hvalue)
  | and =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ &&& value =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ &&& value := by
        rw [hrelation.register sourceName hsource (valid sourceName hsource)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨sourceName, hsource⟩ &&& value)
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ &&& value) hvalue)
  | or =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ ||| value =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ||| value := by
        rw [hrelation.register sourceName hsource (valid sourceName hsource)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨sourceName, hsource⟩ ||| value)
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ||| value) hvalue)
  | xor =>
      have hvalue :
          readRegister source ⟨sourceName, hsource⟩ ^^^ value =
            readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ^^^ value := by
        rw [hrelation.register sourceName hsource (valid sourceName hsource)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (readRegister source ⟨sourceName, hsource⟩ ^^^ value)
          (readRegister target ⟨colour sourceName, valid sourceName hsource⟩ ^^^ value) hvalue)

theorem evalWordProg_assignBinaryVarConst_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : BinOp) (name sourceName : Nat) (value : Word width)
    (hname : name < 32) (hsource : sourceName < 32) :
    ∃ source' target',
      evalWordProg source
          (.assign name (.op operator [.var sourceName, .const value])) = some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.op operator [.var sourceName, .const value]))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  cases operator with
  | add =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .add [.var sourceName, .const value])) =
            some (execute source (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ value)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .add [.var sourceName, .const value]))) =
            some (execute target
              (.addi ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid sourceName hsource,
          executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeImmediateBinary colour valid injective colourZero
          source target hrelation .add name sourceName value hname hsource⟩
  | sub =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .sub [.var sourceName, .const value])) =
            some (execute source (.addi ⟨name, hname⟩ ⟨sourceName, hsource⟩ (0 - value))) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .sub [.var sourceName, .const value]))) =
            some (execute target
              (.addi ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ (0 - value))) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid sourceName hsource,
          executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeImmediateBinary colour valid injective colourZero
          source target hrelation .sub name sourceName value hname hsource⟩
  | and =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .and [.var sourceName, .const value])) =
            some (execute source (.andi ⟨name, hname⟩ ⟨sourceName, hsource⟩ value)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .and [.var sourceName, .const value]))) =
            some (execute target
              (.andi ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid sourceName hsource,
          executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeImmediateBinary colour valid injective colourZero
          source target hrelation .and name sourceName value hname hsource⟩
  | or =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .or [.var sourceName, .const value])) =
            some (execute source (.ori ⟨name, hname⟩ ⟨sourceName, hsource⟩ value)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .or [.var sourceName, .const value]))) =
            some (execute target
              (.ori ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid sourceName hsource,
          executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeImmediateBinary colour valid injective colourZero
          source target hrelation .or name sourceName value hname hsource⟩
  | xor =>
      have hsourceEval :
          evalWordProg source (.assign name (.op .xor [.var sourceName, .const value])) =
            some (execute source (.xori ⟨name, hname⟩ ⟨sourceName, hsource⟩ value)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hsource, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.op .xor [.var sourceName, .const value]))) =
            some (execute target
              (.xori ⟨colour name, valid name hname⟩
                ⟨colour sourceName, valid sourceName hsource⟩ value)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid sourceName hsource,
          executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeImmediateBinary colour valid injective colourZero
          source target hrelation .xor name sourceName value hname hsource⟩

theorem wordColourStateRelation_executeSllForRotate
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name left right : Nat) (hname : name < 32) (hleft : left < 32)
    (hright : right < 32) :
    WordColourStateRelation colour
      (execute source (.sll ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
      (execute target (.sll ⟨colour name, valid name hname⟩
        ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
  have hvalue :
      BitVec.shiftLeft (readRegister source ⟨left, hleft⟩)
          (shiftAmount (readRegister source ⟨right, hright⟩)) =
        BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
          (shiftAmount (readRegister target ⟨colour right, valid right hright⟩)) := by
    rw [hrelation.register left hleft (valid left hleft),
      hrelation.register right hright (valid right hright)]
  have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
  simpa [execute] using
    (wordColourStateRelation_writeRegister colour valid injective colourZero
      {source with pc := nextPc source} {target with pc := nextPc target}
      hnext name hname
      (BitVec.shiftLeft (readRegister source ⟨left, hleft⟩)
        (shiftAmount (readRegister source ⟨right, hright⟩)))
      (BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
        (shiftAmount (readRegister target ⟨colour right, valid right hright⟩))) hvalue)

theorem wordColourStateRelation_executeSrlForRotate
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name left right : Nat) (hname : name < 32) (hleft : left < 32)
    (hright : right < 32) :
    WordColourStateRelation colour
      (execute source (.srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
      (execute target (.srl ⟨colour name, valid name hname⟩
        ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
  have hvalue :
      BitVec.ushiftRight (readRegister source ⟨left, hleft⟩)
          (shiftAmount (readRegister source ⟨right, hright⟩)) =
        BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
          (shiftAmount (readRegister target ⟨colour right, valid right hright⟩)) := by
    rw [hrelation.register left hleft (valid left hleft),
      hrelation.register right hright (valid right hright)]
  have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
  simpa [execute] using
    (wordColourStateRelation_writeRegister colour valid injective colourZero
      {source with pc := nextPc source} {target with pc := nextPc target}
      hnext name hname
      (BitVec.ushiftRight (readRegister source ⟨left, hleft⟩)
        (shiftAmount (readRegister source ⟨right, hright⟩)))
      (BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
        (shiftAmount (readRegister target ⟨colour right, valid right hright⟩))) hvalue)

theorem wordColourStateRelation_executeRotateRight
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (colourScratch : colour 31 = 31)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name left right : Nat) (hname : name < 32) (hleft : left < 32)
    (hright : right < 32) (hnameScratch : name ≠ 31)
    (hleftScratch : left ≠ 31) (hrightScratch : right ≠ 31) :
    WordColourStateRelation colour
      (executeInstructions source
        [.ori 31 0 (BitVec.ofNat width width), .sub 31 31 ⟨right, hright⟩,
          .sll 31 ⟨left, hleft⟩ 31, .srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩,
          .or ⟨name, hname⟩ ⟨name, hname⟩ 31])
      (executeInstructions target
        [.ori ⟨colour 31, valid 31 (by omega)⟩ ⟨colour 0, valid 0 (by omega)⟩
            (BitVec.ofNat width width),
          .sub ⟨colour 31, valid 31 (by omega)⟩ ⟨colour 31, valid 31 (by omega)⟩
            ⟨colour right, valid right hright⟩,
          .sll ⟨colour 31, valid 31 (by omega)⟩ ⟨colour left, valid left hleft⟩
            ⟨colour 31, valid 31 (by omega)⟩,
          .srl ⟨colour name, valid name hname⟩ ⟨colour left, valid left hleft⟩
            ⟨colour right, valid right hright⟩,
          .or ⟨colour name, valid name hname⟩ ⟨colour name, valid name hname⟩
            ⟨colour 31, valid 31 (by omega)⟩]) := by
  have hnameColourScratch : colour name ≠ 31 := by
    intro h
    apply hnameScratch
    apply injective
    simpa [colourScratch] using h
  have hleftColourScratch : colour left ≠ 31 := by
    intro h
    apply hleftScratch
    apply injective
    simpa [colourScratch] using h
  have hrightColourScratch : colour right ≠ 31 := by
    intro h
    apply hrightScratch
    apply injective
    simpa [colourScratch] using h
  have h1 := wordColourStateRelation_executeImmediateBinary colour valid
    injective colourZero source target hrelation .or 31 0 (BitVec.ofNat width width)
      (by omega) (by omega)
  have h1' :
      WordColourStateRelation colour
        (execute source (.ori 31 0 (BitVec.ofNat width width)))
        (execute target (.ori 31 0 (BitVec.ofNat width width))) := by
    simpa [colourScratch, colourZero] using h1
  have h2 := wordColourStateRelation_executeBinary colour valid injective colourZero
    (execute source (.ori 31 0 (BitVec.ofNat width width)))
    (execute target (.ori 31 0 (BitVec.ofNat width width))) h1' .sub 31 31 right
      (by omega) (by omega) hright
  have h2' :
      WordColourStateRelation colour
        (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
          (.sub 31 31 ⟨right, hright⟩))
        (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
          (.sub 31 31 ⟨colour right, valid right hright⟩)) := by
    simpa [colourScratch] using h2
  have h3 := wordColourStateRelation_executeSllForRotate colour valid injective colourZero
    (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
      (.sub 31 31 ⟨right, hright⟩))
    (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
      (.sub 31 31 ⟨colour right, valid right hright⟩)) h2' 31 left 31
      (by omega) hleft (by omega)
  have h3' :
      WordColourStateRelation colour
        (execute
          (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
            (.sub 31 31 ⟨right, hright⟩))
          (.sll 31 ⟨left, hleft⟩ 31))
        (execute
          (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
            (.sub 31 31 ⟨colour right, valid right hright⟩))
          (.sll 31 ⟨colour left, valid left hleft⟩ 31)) := by
    simpa [colourScratch] using h3
  have h4 := wordColourStateRelation_executeSrlForRotate colour valid injective colourZero
    (execute
      (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
        (.sub 31 31 ⟨right, hright⟩))
      (.sll 31 ⟨left, hleft⟩ 31))
    (execute
      (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
        (.sub 31 31 ⟨colour right, valid right hright⟩))
      (.sll 31 ⟨colour left, valid left hleft⟩ 31)) h3' name left right
      hname hleft hright
  have h4' :
      WordColourStateRelation colour
        (execute
          (execute
            (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
              (.sub 31 31 ⟨right, hright⟩))
            (.sll 31 ⟨left, hleft⟩ 31))
          (.srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
        (execute
          (execute
            (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
              (.sub 31 31 ⟨colour right, valid right hright⟩))
            (.sll 31 ⟨colour left, valid left hleft⟩ 31))
          (.srl ⟨colour name, valid name hname⟩ ⟨colour left, valid left hleft⟩
            ⟨colour right, valid right hright⟩)) := by
    simpa [colourScratch] using h4
  have h5 := wordColourStateRelation_executeBinary colour valid injective colourZero
    (execute
      (execute
        (execute (execute source (.ori 31 0 (BitVec.ofNat width width)))
          (.sub 31 31 ⟨right, hright⟩))
        (.sll 31 ⟨left, hleft⟩ 31))
      (.srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
    (execute
      (execute
        (execute (execute target (.ori 31 0 (BitVec.ofNat width width)))
          (.sub 31 31 ⟨colour right, valid right hright⟩))
        (.sll 31 ⟨colour left, valid left hleft⟩ 31))
      (.srl ⟨colour name, valid name hname⟩ ⟨colour left, valid left hleft⟩
        ⟨colour right, valid right hright⟩)) h4' .or name name 31
      (by omega) hname (by omega)
  simpa [executeInstructions, colourScratch, colourZero] using h5

theorem evalWordProg_assignRotateRight_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (colourScratch : colour 31 = 31)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (name left right : Nat) (hname : name < 32) (hleft : left < 32)
    (hright : right < 32) (hnameScratch : name ≠ 31)
    (hleftScratch : left ≠ 31) (hrightScratch : right ≠ 31) :
    ∃ source' target',
      evalWordProg source
          (.assign name (.shift .ror (.var left) (.var right))) = some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.shift .ror (.var left) (.var right)))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  have hsourceEval :
      evalWordProg source (.assign name (.shift .ror (.var left) (.var right))) =
        some (executeInstructions source
          [.ori 31 0 (BitVec.ofNat width width), .sub 31 31 ⟨right, hright⟩,
            .sll 31 ⟨left, hleft⟩ 31, .srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩,
            .or ⟨name, hname⟩ ⟨name, hname⟩ 31]) := by
    simp [evalWordProg, wordExpToInstructions, 
      registerOfNat, hname, hleft, hright, hnameScratch, hleftScratch,
      hrightScratch, executeInstructions]
  have hnameColourScratch : colour name ≠ 31 := by
    intro h
    apply hnameScratch
    apply injective
    simpa [colourScratch] using h
  have hleftColourScratch : colour left ≠ 31 := by
    intro h
    apply hleftScratch
    apply injective
    simpa [colourScratch] using h
  have hrightColourScratch : colour right ≠ 31 := by
    intro h
    apply hrightScratch
    apply injective
    simpa [colourScratch] using h
  have htargetEval :
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.shift .ror (.var left) (.var right)))) =
        some (executeInstructions target
          [.ori 31 0 (BitVec.ofNat width width),
            .sub 31 31 ⟨colour right, valid right hright⟩,
            .sll 31 ⟨colour left, valid left hleft⟩ 31,
            .srl ⟨colour name, valid name hname⟩ ⟨colour left, valid left hleft⟩
              ⟨colour right, valid right hright⟩,
            .or ⟨colour name, valid name hname⟩ ⟨colour name, valid name hname⟩ 31]) := by
    simp [evalWordProg, wordApplyColour, wordApplyColourExp,
      wordExpToInstructions, registerOfNat,
      
      valid name hname, valid left hleft, valid right hright,
      hnameColourScratch, hleftColourScratch, hrightColourScratch,
      executeInstructions]
  refine ⟨_, _, hsourceEval, htargetEval, ?_⟩
  simpa [colourScratch, colourZero] using
    (wordColourStateRelation_executeRotateRight colour valid injective colourZero
      colourScratch source target hrelation name left right hname hleft hright
      hnameScratch hleftScratch hrightScratch)

theorem wordColourStateRelation_executeShiftImmediate
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : Shift) (name left : Nat) (amount : Word width)
    (hoperator : operator ≠ .ror) (hname : name < 32) (hleft : left < 32) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .lsl => .slli ⟨name, hname⟩ ⟨left, hleft⟩ amount
        | .lsr => .srli ⟨name, hname⟩ ⟨left, hleft⟩ amount
        | .asr => .srai ⟨name, hname⟩ ⟨left, hleft⟩ amount
        | .ror => .slli ⟨name, hname⟩ ⟨left, hleft⟩ amount))
      (execute target (match operator with
        | .lsl => .slli ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ amount
        | .lsr => .srli ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ amount
        | .asr => .srai ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ amount
        | .ror => .slli ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ amount)) := by
  cases operator with
  | lsl =>
      have hvalue :
          BitVec.shiftLeft (readRegister source ⟨left, hleft⟩) (shiftAmount amount) =
            BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount amount) := by
        rw [hrelation.register left hleft (valid left hleft)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (BitVec.shiftLeft (readRegister source ⟨left, hleft⟩) (shiftAmount amount))
          (BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount amount)) hvalue)
  | lsr =>
      have hvalue :
          BitVec.ushiftRight (readRegister source ⟨left, hleft⟩) (shiftAmount amount) =
            BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount amount) := by
        rw [hrelation.register left hleft (valid left hleft)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (BitVec.ushiftRight (readRegister source ⟨left, hleft⟩) (shiftAmount amount))
          (BitVec.ushiftRight (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount amount)) hvalue)
  | asr =>
      have hvalue :
          BitVec.sshiftRight (readRegister source ⟨left, hleft⟩) (shiftAmount amount) =
            BitVec.sshiftRight (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount amount) := by
        rw [hrelation.register left hleft (valid left hleft)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (BitVec.sshiftRight (readRegister source ⟨left, hleft⟩) (shiftAmount amount))
          (BitVec.sshiftRight (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount amount)) hvalue)
  | ror => exact (hoperator rfl).elim

theorem evalWordProg_assignShiftVarConst_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : Shift) (name left : Nat) (amount : Word width)
    (hoperator : operator ≠ .ror) (hname : name < 32) (hleft : left < 32) :
    ∃ source' target',
      evalWordProg source
          (.assign name (.shift operator (.var left) (.const amount))) = some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.shift operator (.var left) (.const amount)))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  cases operator with
  | lsl =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .lsl (.var left) (.const amount))) =
            some (execute source (.slli ⟨name, hname⟩ ⟨left, hleft⟩ amount)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .lsl (.var left) (.const amount)))) =
            some (execute target
              (.slli ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ amount)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShiftImmediate colour valid injective colourZero
          source target hrelation .lsl name left amount hoperator hname hleft⟩
  | lsr =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .lsr (.var left) (.const amount))) =
            some (execute source (.srli ⟨name, hname⟩ ⟨left, hleft⟩ amount)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .lsr (.var left) (.const amount)))) =
            some (execute target
              (.srli ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ amount)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShiftImmediate colour valid injective colourZero
          source target hrelation .lsr name left amount hoperator hname hleft⟩
  | asr =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .asr (.var left) (.const amount))) =
            some (execute source (.srai ⟨name, hname⟩ ⟨left, hleft⟩ amount)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .asr (.var left) (.const amount)))) =
            some (execute target
              (.srai ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ amount)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShiftImmediate colour valid injective colourZero
          source target hrelation .asr name left amount hoperator hname hleft⟩
  | ror => exact (hoperator rfl).elim

theorem wordColourStateRelation_executeShift
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : Shift) (name left right : Nat) (hoperator : operator ≠ .ror)
    (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
    WordColourStateRelation colour
      (execute source (match operator with
        | .lsl => .sll ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .lsr => .srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .asr => .sra ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩
        | .ror => .sll ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩))
      (execute target (match operator with
        | .lsl => .sll ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .lsr => .srl ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .asr => .sra ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩
        | .ror => .sll ⟨colour name, valid name hname⟩
            ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
  cases operator with
  | lsl =>
      have hvalue :
          BitVec.shiftLeft (readRegister source ⟨left, hleft⟩)
              (shiftAmount (readRegister source ⟨right, hright⟩)) =
            BitVec.shiftLeft (readRegister target ⟨colour left, valid left hleft⟩)
              (shiftAmount (readRegister target ⟨colour right, valid right hright⟩)) := by
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
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
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
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
        rw [hrelation.register left hleft (valid left hleft),
          hrelation.register right hright (valid right hright)]
      have hnext := wordColourStateRelation_nextPc colour valid source target hrelation
      simpa [execute] using
        (wordColourStateRelation_writeRegister colour valid injective colourZero
          {source with pc := nextPc source} {target with pc := nextPc target}
          hnext name hname
          (BitVec.sshiftRight (readRegister source ⟨left, hleft⟩)
            (shiftAmount (readRegister source ⟨right, hright⟩)))
          (BitVec.sshiftRight (readRegister target ⟨colour left, valid left hleft⟩)
            (shiftAmount (readRegister target ⟨colour right, valid right hright⟩))) hvalue)
  | ror => exact (hoperator rfl).elim

theorem evalWordProg_assignShiftVarVar_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (operator : Shift) (name left right : Nat) (hoperator : operator ≠ .ror)
    (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
    ∃ source' target',
      evalWordProg source
          (.assign name (.shift operator (.var left) (.var right))) = some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.assign name (.shift operator (.var left) (.var right)))) = some target' ∧
      WordColourStateRelation colour source' target' := by
  cases operator with
  | lsl =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .lsl (.var left) (.var right))) =
            some (execute source (.sll ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .lsl (.var left) (.var right)))) =
            some (execute target
              (.sll ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShift colour valid injective colourZero
          source target hrelation .lsl name left right hoperator hname hleft hright⟩
  | lsr =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .lsr (.var left) (.var right))) =
            some (execute source (.srl ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .lsr (.var left) (.var right)))) =
            some (execute target
              (.srl ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShift colour valid injective colourZero
          source target hrelation .lsr name left right hoperator hname hleft hright⟩
  | asr =>
      have hsourceEval :
          evalWordProg source (.assign name (.shift .asr (.var left) (.var right))) =
            some (execute source (.sra ⟨name, hname⟩ ⟨left, hleft⟩ ⟨right, hright⟩)) := by
        simp [evalWordProg, wordExpToInstructions, wordExpToInstruction,
          registerOfNat, hname, hleft, hright, executeInstructions]
      have htargetEval :
          evalWordProg target
              (wordApplyColour colour
                (.assign name (.shift .asr (.var left) (.var right)))) =
            some (execute target
              (.sra ⟨colour name, valid name hname⟩
                ⟨colour left, valid left hleft⟩ ⟨colour right, valid right hright⟩)) := by
        simp [evalWordProg, wordApplyColour, wordApplyColourExp,
          wordExpToInstructions, wordExpToInstruction, registerOfNat,
          valid name hname, valid left hleft,
          valid right hright, executeInstructions]
      exact ⟨_, _, hsourceEval, htargetEval,
        wordColourStateRelation_executeShift colour valid injective colourZero
          source target hrelation .asr name left right hoperator hname hleft hright⟩
  | ror => exact (hoperator rfl).elim

theorem evalWordProg_moveOne_applyColour [NeZero width]
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelation colour source target)
    (name sourceName : Nat) (hname : name < 32) (hsource : sourceName < 32)
    (hname31 : name ≠ 31) (hsource31 : sourceName ≠ 31)
    (hcolourName31 : colour name ≠ 31) (hcolourSource31 : colour sourceName ≠ 31)
    (hne : name ≠ sourceName) :
    ∃ source' target',
      evalWordProg source (.move 1 [(name, sourceName)]) = some source' ∧
      evalWordProg target
          (wordApplyColour colour (.move 1 [(name, sourceName)])) = some target' ∧
      WordColourStateRelation colour source' target' := by
  have hne' : sourceName ≠ name := Ne.symm hne
  have hcolourNe : colour name ≠ colour sourceName := fun heq =>
    hne (injective heq)
  have hcolourNe' : colour sourceName ≠ colour name := Ne.symm hcolourNe
  have hsourceMove :
      evalWordProg source (.move 1 [(name, sourceName)]) =
        evalWordProg source (.assign name (.var sourceName)) := by
    simp [evalWordProg, wordMoveToInstructions, wordMoveToInstructionsAux,
      wordMoveRegisterDestinations, wordMoveRegisterReady,
      wordMoveRegisterRemoveDestination, wordExpToInstructions,
      wordExpToInstruction, registerOfNat, hname, hsource, hname31, hsource31,
      hne']
  have htargetMove :
      evalWordProg target
          (wordApplyColour colour (.move 1 [(name, sourceName)])) =
        evalWordProg target
          (.assign (colour name) (.var (colour sourceName))) := by
    simp [evalWordProg, wordApplyColour, wordMoveToInstructions,
      wordMoveToInstructionsAux, wordMoveRegisterDestinations,
      wordMoveRegisterReady, wordMoveRegisterRemoveDestination,
      wordExpToInstructions, wordExpToInstruction, registerOfNat,
      valid name hname, valid sourceName hsource, hcolourName31,
      hcolourSource31, hcolourNe']
  rcases evalWordProg_assignVar_applyColour colour valid injective colourZero
      source target hrelation name sourceName hname hsource with
    ⟨source', target', hsource', htarget', hrelation'⟩
  refine ⟨source', target', hsourceMove.trans hsource', ?_, hrelation'⟩
  exact htargetMove.trans (by simpa [wordApplyColour, wordApplyColourExp]
    using htarget')

theorem evalWordProg_moveTwo_applyColour [NeZero width]
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (source target : State width)
    (hrelation : WordColourStateRelation colour source target)
    (destinationOne sourceOne destinationTwo sourceTwo : Nat)
    (hdestinationOne : destinationOne < 32) (hsourceOne : sourceOne < 32)
    (hdestinationTwo : destinationTwo < 32) (hsourceTwo : sourceTwo < 32)
    (hdestinationOne31 : destinationOne ≠ 31) (hsourceOne31 : sourceOne ≠ 31)
    (hdestinationTwo31 : destinationTwo ≠ 31) (hsourceTwo31 : sourceTwo ≠ 31)
    (hcolourDestinationOne31 : colour destinationOne ≠ 31)
    (hcolourSourceOne31 : colour sourceOne ≠ 31)
    (hcolourDestinationTwo31 : colour destinationTwo ≠ 31)
    (hcolourSourceTwo31 : colour sourceTwo ≠ 31)
    (hdestinations : destinationOne ≠ destinationTwo)
    (hsourceOneDestinationOne : sourceOne ≠ destinationOne)
    (hsourceOneDestinationTwo : sourceOne ≠ destinationTwo)
    (hsourceTwoDestinationOne : sourceTwo ≠ destinationOne)
    (hsourceTwoDestinationTwo : sourceTwo ≠ destinationTwo) :
    ∃ source' target',
      evalWordProg source
          (.move 1 [(destinationOne, sourceOne), (destinationTwo, sourceTwo)]) =
        some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.move 1 [(destinationOne, sourceOne), (destinationTwo, sourceTwo)])) =
        some target' ∧
      WordColourStateRelation colour source' target' := by
  have hdestinationTwoOne : destinationTwo ≠ destinationOne := Ne.symm hdestinations
  have hsourceOneDestinationOne' : destinationOne ≠ sourceOne :=
    Ne.symm hsourceOneDestinationOne
  have hsourceTwoDestinationTwo' : destinationTwo ≠ sourceTwo :=
    Ne.symm hsourceTwoDestinationTwo
  have hcolourDestinations : colour destinationOne ≠ colour destinationTwo := fun heq =>
    hdestinations (injective heq)
  have hcolourDestinations' : colour destinationTwo ≠ colour destinationOne :=
    Ne.symm hcolourDestinations
  have hcolourSourceOneDestinationOne : colour sourceOne ≠ colour destinationOne := fun heq =>
    hsourceOneDestinationOne (injective heq)
  have hcolourSourceOneDestinationTwo : colour sourceOne ≠ colour destinationTwo := fun heq =>
    hsourceOneDestinationTwo (injective heq)
  have hcolourSourceTwoDestinationOne : colour sourceTwo ≠ colour destinationOne := fun heq =>
    hsourceTwoDestinationOne (injective heq)
  have hcolourSourceTwoDestinationTwo : colour sourceTwo ≠ colour destinationTwo := fun heq =>
    hsourceTwoDestinationTwo (injective heq)
  have executeInstructions_two (state : State width)
      (first second : Instruction width) :
      executeInstructions state [first, second] = execute (execute state first) second := by
    simpa only [List.singleton_append, executeInstructions_single] using
      (executeInstructions_append state [first] [second])
  have hsourceMove :
      evalWordProg source
          (.move 1 [(destinationOne, sourceOne), (destinationTwo, sourceTwo)]) =
        evalWordProg source
          (.seq (.move 1 [(destinationOne, sourceOne)])
            (.move 1 [(destinationTwo, sourceTwo)])) := by
    simp [evalWordProg, wordMoveToInstructions, wordMoveToInstructionsAux,
      wordMoveRegisterDestinations, wordMoveRegisterReady,
      wordMoveRegisterRemoveDestination, wordExpToInstructions,
      wordExpToInstruction, registerOfNat, hdestinationOne, hsourceOne,
      hdestinationTwo, hsourceTwo, hdestinationOne31, hsourceOne31,
      hdestinationTwo31, hsourceTwo31, hdestinations,
      hdestinationTwoOne, hsourceOneDestinationOne,
      hsourceOneDestinationTwo, hsourceTwoDestinationTwo,
      executeInstructions_two]
  have htargetMove :
      evalWordProg target
          (wordApplyColour colour
            (.move 1 [(destinationOne, sourceOne), (destinationTwo, sourceTwo)])) =
        evalWordProg target
          (.seq
            (.move 1 [(colour destinationOne, colour sourceOne)])
            (.move 1 [(colour destinationTwo, colour sourceTwo)])) := by
    simp [evalWordProg, wordApplyColour, wordMoveToInstructions,
      wordMoveToInstructionsAux, wordMoveRegisterDestinations,
      wordMoveRegisterReady, wordMoveRegisterRemoveDestination,
      wordExpToInstructions, wordExpToInstruction, registerOfNat,
      valid destinationOne hdestinationOne, valid sourceOne hsourceOne,
      valid destinationTwo hdestinationTwo, valid sourceTwo hsourceTwo,
      hcolourDestinationOne31, hcolourSourceOne31,
      hcolourDestinationTwo31, hcolourSourceTwo31, hcolourDestinations,
      hcolourDestinations', hcolourSourceOneDestinationOne,
      hcolourSourceOneDestinationTwo, hcolourSourceTwoDestinationTwo,
      executeInstructions_two]
  rcases evalWordProg_moveOne_applyColour colour valid injective colourZero
      source target hrelation destinationOne sourceOne hdestinationOne hsourceOne
      hdestinationOne31 hsourceOne31 hcolourDestinationOne31 hcolourSourceOne31
      hsourceOneDestinationOne' with
    ⟨sourceMiddle, targetMiddle, hsourceOneEval, htargetOneEval, hrelationMiddle⟩
  rcases evalWordProg_moveOne_applyColour colour valid injective colourZero
      sourceMiddle targetMiddle hrelationMiddle destinationTwo sourceTwo
      hdestinationTwo hsourceTwo hdestinationTwo31 hsourceTwo31
      hcolourDestinationTwo31 hcolourSourceTwo31 hsourceTwoDestinationTwo' with
    ⟨source', target', hsourceTwoEval, htargetTwoEval, hrelation'⟩
  have htargetOneEval' :
      evalWordProg target
          (.move 1 [(colour destinationOne, colour sourceOne)]) = some targetMiddle := by
    simpa [wordApplyColour, wordApplyColourExp] using htargetOneEval
  have htargetTwoEval' :
      evalWordProg targetMiddle
          (.move 1 [(colour destinationTwo, colour sourceTwo)]) = some target' := by
    simpa [wordApplyColour, wordApplyColourExp] using htargetTwoEval
  refine ⟨source', target', hsourceMove.trans ?_, htargetMove.trans ?_, hrelation'⟩
  · rw [evalWordProg]
    rw [hsourceOneEval]
    simpa using hsourceTwoEval
  · rw [evalWordProg]
    rw [htargetOneEval']
    simpa using htargetTwoEval'

inductive WordVarStraightLine (width : Nat) : WordProg (Word width) → Prop where
  | skip : WordVarStraightLine width .skip
  | moveOne (name source : Nat) (hname : name < 32) (hsource : source < 32)
      (hname31 : name ≠ 31) (hsource31 : source ≠ 31)
      (hne : name ≠ source) :
      WordVarStraightLine width (.move 1 [(name, source)])
  | moveTwo (destinationOne sourceOne destinationTwo sourceTwo : Nat)
      (hdestinationOne : destinationOne < 32) (hsourceOne : sourceOne < 32)
      (hdestinationTwo : destinationTwo < 32) (hsourceTwo : sourceTwo < 32)
      (hdestinationOne31 : destinationOne ≠ 31) (hsourceOne31 : sourceOne ≠ 31)
      (hdestinationTwo31 : destinationTwo ≠ 31) (hsourceTwo31 : sourceTwo ≠ 31)
      (hdestinations : destinationOne ≠ destinationTwo)
      (hsourceOneDestinationOne : sourceOne ≠ destinationOne)
      (hsourceOneDestinationTwo : sourceOne ≠ destinationTwo)
      (hsourceTwoDestinationOne : sourceTwo ≠ destinationOne)
      (hsourceTwoDestinationTwo : sourceTwo ≠ destinationTwo) :
      WordVarStraightLine width
        (.move 1 [(destinationOne, sourceOne), (destinationTwo, sourceTwo)])
  | assign (name source : Nat) (hname : name < 32) (hsource : source < 32) :
      WordVarStraightLine width (.assign name (.var source))
  | assignConst (name : Nat) (value : Word width) (hname : name < 32) :
      WordVarStraightLine width (.assign name (.const value))
  | assignBinary (operator : BinOp) (name left right : Nat)
      (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
      WordVarStraightLine width (.assign name (.op operator [.var left, .var right]))
  | assignImmediate (operator : BinOp) (name source : Nat) (value : Word width)
      (hname : name < 32) (hsource : source < 32) :
      WordVarStraightLine width (.assign name (.op operator [.var source, .const value]))
  | assignShift (operator : Shift) (name left right : Nat) (hoperator : operator ≠ .ror)
      (hname : name < 32) (hleft : left < 32) (hright : right < 32) :
      WordVarStraightLine width (.assign name (.shift operator (.var left) (.var right)))
  | assignShiftImmediate (operator : Shift) (name left : Nat) (amount : Word width)
      (hoperator : operator ≠ .ror) (hname : name < 32) (hleft : left < 32) :
      WordVarStraightLine width (.assign name (.shift operator (.var left) (.const amount)))
  | seq {first second : WordProg (Word width)} :
      WordVarStraightLine width first → WordVarStraightLine width second →
      WordVarStraightLine width (.seq first second)

/-! Every coloured program in the restricted variable straight-line fragment
    is also accepted by the backend's structural straight-line contract.  The
    latter deliberately permits a wider set of leaves; this bridge lets the
    allocator simulation be composed with the generic Word-to-RISC-V soundness
    theorem without duplicating the backend grammar. -/

theorem wordVarStraightLine_to_wordRiscVStraightLine [NeZero width]
    (colour : Nat → Nat) (program : WordProg (Word width))
    (hprogram : WordVarStraightLine width program) :
    WordRiscVStraightLine (wordApplyColour colour program) := by
  induction hprogram with
  | skip => simpa [wordApplyColour] using (WordRiscVStraightLine.skip :
      WordRiscVStraightLine (.skip : WordProg (Word width)))
  | moveOne name source _ _ _ _ _ => simpa [wordApplyColour] using (WordRiscVStraightLine.move 1
      [(colour name, colour source)] : WordRiscVStraightLine
        (.move 1 [(colour name, colour source)]))
  | moveTwo destinationOne sourceOne destinationTwo sourceTwo _ _ _ _ _ _ _ _ _ _ _ =>
      simpa [wordApplyColour] using (WordRiscVStraightLine.move 1
      [(colour destinationOne, colour sourceOne),
       (colour destinationTwo, colour sourceTwo)] : WordRiscVStraightLine
        (.move 1 [(colour destinationOne, colour sourceOne),
          (colour destinationTwo, colour sourceTwo)]))
  | assign name source _ _ => simpa [wordApplyColour, wordApplyColourExp] using
      (WordRiscVStraightLine.assign
      (colour name) (WordExp.var (colour source)) : WordRiscVStraightLine
        (.assign (colour name) (.var (colour source))))
  | assignConst name value _ => simpa [wordApplyColour, wordApplyColourExp] using
      (WordRiscVStraightLine.assign
      (colour name) (WordExp.const value) : WordRiscVStraightLine
        (.assign (colour name) (.const value)))
  | assignBinary operator name left right _ _ _ =>
      simpa [wordApplyColour, wordApplyColourExp] using (WordRiscVStraightLine.assign
      (colour name) (WordExp.op operator [.var (colour left), .var (colour right)]) :
        WordRiscVStraightLine
          (.assign (colour name) (.op operator [.var (colour left), .var (colour right)])))
  | assignImmediate operator name source value _ _ =>
      simpa [wordApplyColour, wordApplyColourExp] using (WordRiscVStraightLine.assign
      (colour name) (WordExp.op operator [.var (colour source), .const value]) :
        WordRiscVStraightLine
          (.assign (colour name) (.op operator [.var (colour source), .const value])))
  | assignShift operator name left right _ _ _ _ =>
      simpa [wordApplyColour, wordApplyColourExp] using (WordRiscVStraightLine.assign
      (colour name) (WordExp.shift operator (.var (colour left)) (.var (colour right))) :
        WordRiscVStraightLine
          (.assign (colour name) (.shift operator (.var (colour left)) (.var (colour right)))))
  | assignShiftImmediate operator name left amount _ _ _ =>
      simpa [wordApplyColour, wordApplyColourExp] using
      (WordRiscVStraightLine.assign (colour name)
        (WordExp.shift operator (.var (colour left)) (.const amount)) :
        WordRiscVStraightLine
          (.assign (colour name) (.shift operator (.var (colour left)) (.const amount))))
  | seq _ _ ihFirst ihSecond => simpa [wordApplyColour] using
      (WordRiscVStraightLine.seq _ _ ihFirst ihSecond)

theorem evalWordProg_wordVarStraightLine_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (colourNoScratch : ∀ name, name < 31 → colour name ≠ 31)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation colour source target)
    (program : WordProg (Word width))
    (hprogram : WordVarStraightLine width program) :
    ∃ source' target', evalWordProg source program = some source' ∧
      evalWordProg target (wordApplyColour colour program) = some target' ∧
      WordColourStateRelation colour source' target' := by
  induction hprogram generalizing source target with
  | skip =>
      exact ⟨source, target, by simp [evalWordProg],
        by simp [evalWordProg, wordApplyColour], hrelation⟩
  | moveOne name sourceName hname hsource hname31 hsource31 hne =>
      have hnameLT31 : name < 31 := by omega
      have hsourceLT31 : sourceName < 31 := by omega
      exact evalWordProg_moveOne_applyColour colour valid injective colourZero
        source target hrelation name sourceName hname hsource hname31 hsource31
        (colourNoScratch name hnameLT31) (colourNoScratch sourceName hsourceLT31) hne
  | moveTwo destinationOne sourceOne destinationTwo sourceTwo
      hdestinationOne hsourceOne hdestinationTwo hsourceTwo
      hdestinationOne31 hsourceOne31 hdestinationTwo31 hsourceTwo31
      hdestinations hsourceOneDestinationOne hsourceOneDestinationTwo
      hsourceTwoDestinationOne hsourceTwoDestinationTwo =>
      have hdestinationOneLT31 : destinationOne < 31 := by omega
      have hsourceOneLT31 : sourceOne < 31 := by omega
      have hdestinationTwoLT31 : destinationTwo < 31 := by omega
      have hsourceTwoLT31 : sourceTwo < 31 := by omega
      exact evalWordProg_moveTwo_applyColour colour valid injective colourZero
        source target hrelation destinationOne sourceOne destinationTwo sourceTwo
        hdestinationOne hsourceOne hdestinationTwo hsourceTwo
        hdestinationOne31 hsourceOne31 hdestinationTwo31 hsourceTwo31
        (colourNoScratch destinationOne hdestinationOneLT31)
        (colourNoScratch sourceOne hsourceOneLT31)
        (colourNoScratch destinationTwo hdestinationTwoLT31)
        (colourNoScratch sourceTwo hsourceTwoLT31)
        hdestinations hsourceOneDestinationOne hsourceOneDestinationTwo
        hsourceTwoDestinationOne hsourceTwoDestinationTwo
  | assign name sourceName hname hsource =>
      exact evalWordProg_assignVar_applyColour colour valid injective colourZero
        source target hrelation name sourceName hname hsource
  | assignConst name value hname =>
      exact evalWordProg_assignConst_applyColour colour valid injective colourZero
        source target hrelation name value hname
  | assignBinary operator name left right hname hleft hright =>
      exact evalWordProg_assignBinaryVarVar_applyColour colour valid injective colourZero
        source target hrelation operator name left right hname hleft hright
  | assignImmediate operator name sourceName value hname hsource =>
      exact evalWordProg_assignBinaryVarConst_applyColour colour valid injective colourZero
        source target hrelation operator name sourceName value hname hsource
  | assignShift operator name left right hoperator hname hleft hright =>
      exact evalWordProg_assignShiftVarVar_applyColour colour valid injective colourZero
        source target hrelation operator name left right hoperator hname hleft hright
  | assignShiftImmediate operator name left amount hoperator hname hleft =>
      exact evalWordProg_assignShiftVarConst_applyColour colour valid injective colourZero
        source target hrelation operator name left amount hoperator hname hleft
  | @seq first second hfirst hsecond ihFirst ihSecond =>
      rcases ihFirst source target hrelation with
        ⟨firstSource, firstTarget, hfirstSource, hfirstTarget, hfirstRelation⟩
      rcases ihSecond firstSource firstTarget hfirstRelation with
        ⟨secondSource, secondTarget, hsecondSource, hsecondTarget, hsecondRelation⟩
      refine ⟨secondSource, secondTarget, ?_, ?_, hsecondRelation⟩
      · simp [evalWordProg, hfirstSource, hsecondSource]
      · simp [evalWordProg, wordApplyColour, hfirstTarget, hsecondTarget]

/-! Compose the register-colouring simulation with the executable backend.  A
    successful RISC-V compilation of the coloured program now gives a machine
    state related to the source Word result, rather than stopping at a second
    Word evaluator. -/

theorem evalWordProg_wordVarStraightLine_riscv_simulation [NeZero width]
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (colourNoScratch : ∀ name, name < 31 → colour name ≠ 31)
    (source target : State width)
    (hrelation : WordColourStateRelation colour source target)
    (program : WordProg (Word width))
    (hprogram : WordVarStraightLine width program)
    (code : List (Instruction width))
    (hcompile : wordProgToRiscV (wordApplyColour colour program) = some code) :
    ∃ source' target',
      evalWordProg source program = some source' ∧
      executeInstructions target code = target' ∧
      WordColourStateRelation colour source' target' := by
  rcases evalWordProg_wordVarStraightLine_applyColour colour valid injective
      colourZero colourNoScratch source target hrelation program hprogram with
    ⟨source', target', hsource, htarget, htargetRelation⟩
  have htargetStraight : WordRiscVStraightLine
      (wordApplyColour colour program) :=
    wordVarStraightLine_to_wordRiscVStraightLine colour program hprogram
  have hmachine := wordProgToRiscV_sound_of_straightLine target
    (wordApplyColour colour program) htargetStraight code hcompile
  have htargetEq : target' = executeInstructions target code :=
    Option.some.inj (htarget.symm.trans hmachine)
  subst target'
  exact ⟨source', executeInstructions target code, hsource, rfl, htargetRelation⟩

/-! The semantic colouring theorem is also a contract for the executable
    allocator boundary: once the clash-tree allocator has produced a context,
    its returned coloured program is exactly the program covered by the
    straight-line simulation theorem. -/

theorem wordAllocateProgramWithClashTreeAndColour_straightLine_simulation
    (slots : List Nat) (program : WordProg (Word width))
    (context : WordContext) (coloured : WordProg (Word width))
    (halloc : wordAllocateProgramWithClashTreeAndColour slots program =
      some (context, coloured))
    (valid : wordColourValid (wordFindVar context))
    (injective : Function.Injective (wordFindVar context))
    (colourZero : wordFindVar context 0 = 0)
    (colourNoScratch : ∀ name, name < 31 → wordFindVar context name ≠ 31)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation (wordFindVar context) source target)
    (hprogram : WordVarStraightLine width program) :
    ∃ source' target', evalWordProg source program = some source' ∧
      evalWordProg target coloured = some target' ∧
      WordColourStateRelation (wordFindVar context) source' target' := by
  simp [wordAllocateProgramWithClashTreeAndColour] at halloc
  rcases halloc with ⟨hcontext, hcontextEq, hcoloured⟩
  rcases hcoloured with ⟨hcontextEq', hcoloured⟩
  subst context
  subst coloured
  exact evalWordProg_wordVarStraightLine_applyColour (wordFindVar hcontext)
    valid injective colourZero colourNoScratch source target hrelation program
    hprogram

/-! The same simulation contract at the executable graph allocator boundary.
    The graph allocator stores its source colouring directly in the returned
    allocation, rather than wrapping it in a WordContext; exposing this
    equation keeps later lowering proofs independent of allocator internals. -/

theorem wordAllocateGraphProgram_straightLine_simulation
    (program : WordProg (Word width))
    (fixedSources : List Nat) (colours stackStart : Nat)
    (allocation : WordGraphAllocation) (coloured : WordProg (Word width))
    (halloc : wordAllocateGraphProgram program fixedSources colours stackStart =
      some (allocation, coloured))
    (valid : wordColourValid (wordGraphColouringAt allocation.colouring))
    (injective : Function.Injective
      (wordGraphColouringAt allocation.colouring))
    (colourZero : wordGraphColouringAt allocation.colouring 0 = 0)
    (colourNoScratch : ∀ name, name < 31 →
      wordGraphColouringAt allocation.colouring name ≠ 31)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation
      (wordGraphColouringAt allocation.colouring) source target)
    (hprogram : WordVarStraightLine width program) :
    ∃ sourcePrime targetPrime, evalWordProg source program = some sourcePrime ∧
      evalWordProg target coloured = some targetPrime ∧
      WordColourStateRelation (wordGraphColouringAt allocation.colouring)
        sourcePrime targetPrime := by
  simp [wordAllocateGraphProgram] at halloc
  rcases halloc with ⟨hallocation, hcoloured⟩
  rcases hcoloured with ⟨_, hEq, hcolour⟩
  have hvalid : wordColourValid (wordGraphColouringAt hallocation.colouring) := by
    simpa [hEq] using valid
  have hinjective : Function.Injective
      (wordGraphColouringAt hallocation.colouring) := by
    simpa [hEq] using injective
  have hzero : wordGraphColouringAt hallocation.colouring 0 = 0 := by
    simpa [hEq] using colourZero
  have hscratch : ∀ name, name < 31 →
      wordGraphColouringAt hallocation.colouring name ≠ 31 := by
    simpa [hEq] using colourNoScratch
  have hrelationHall : WordColourStateRelation
      (wordGraphColouringAt hallocation.colouring) source target := by
    simpa [hEq] using hrelation
  have hresult := evalWordProg_wordVarStraightLine_applyColour
    (wordGraphColouringAt hallocation.colouring) hvalid hinjective hzero
    hscratch source target hrelationHall program hprogram
  rw [hcolour] at hresult
  simpa [hEq] using hresult

/-! Function-level form of the graph-colouring simulation boundary.  The SSA
    renamer and allocator are kept visible in the hypotheses so this theorem
    can be used before the entry moves are lowered. -/

theorem wordAllocateGraphFunction_straightLine_simulation
    (parameters : List Nat) (program : WordProg (Word width))
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (coloured : WordProg (Word width))
    (halloc : wordAllocateGraphFunction parameters program fixedSources
      colours stackStart =
      some (state, renamedParameters, allocation, coloured))
    (valid : wordColourValid (wordGraphColouringAt allocation.colouring))
    (injective : Function.Injective
      (wordGraphColouringAt allocation.colouring))
    (colourZero : wordGraphColouringAt allocation.colouring 0 = 0)
    (colourNoScratch : ∀ name, name < 31 →
      wordGraphColouringAt allocation.colouring name ≠ 31)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation
      (wordGraphColouringAt allocation.colouring) source target)
    (hprogram : WordVarStraightLine width
      (wordSsaRenameFunction parameters program).2.snd) :
    ∃ sourcePrime targetPrime,
      evalWordProg source (wordSsaRenameFunction parameters program).2.snd =
        some sourcePrime ∧
      evalWordProg target coloured = some targetPrime ∧
      WordColourStateRelation (wordGraphColouringAt allocation.colouring)
        sourcePrime targetPrime := by
  simp [wordAllocateGraphFunction] at halloc
  rcases halloc with ⟨a, _, _, _, ha, hcolour⟩
  have hvalid : wordColourValid (wordGraphColouringAt a.colouring) := by
    simpa [ha] using valid
  have hinjective : Function.Injective
      (wordGraphColouringAt a.colouring) := by
    simpa [ha] using injective
  have hzero : wordGraphColouringAt a.colouring 0 = 0 := by
    simpa [ha] using colourZero
  have hscratch : ∀ name, name < 31 →
      wordGraphColouringAt a.colouring name ≠ 31 := by
    simpa [ha] using colourNoScratch
  have hrelationA : WordColourStateRelation
      (wordGraphColouringAt a.colouring) source target := by
    simpa [ha] using hrelation
  have hresult := evalWordProg_wordVarStraightLine_applyColour
    (wordGraphColouringAt a.colouring) hvalid hinjective hzero
    hscratch source target hrelationA
    (wordSsaRenameFunction parameters program).2.snd hprogram
  rw [hcolour] at hresult
  simpa [ha] using hresult

/-! The full-SSA entry variant includes the formal-parameter move prefix in the
    renamed program, so it receives the same executable colouring contract. -/

theorem wordAllocateGraphFunctionWithEntry_straightLine_simulation
    (parameters : List Nat) (program : WordProg (Word width))
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (coloured : WordProg (Word width))
    (halloc : wordAllocateGraphFunctionWithEntry parameters program fixedSources
      colours stackStart =
      some (state, renamedParameters, allocation, coloured))
    (valid : wordColourValid (wordGraphColouringAt allocation.colouring))
    (injective : Function.Injective
      (wordGraphColouringAt allocation.colouring))
    (colourZero : wordGraphColouringAt allocation.colouring 0 = 0)
    (colourNoScratch : ∀ name, name < 31 →
      wordGraphColouringAt allocation.colouring name ≠ 31)
    (source target : State width) [NeZero width]
    (hrelation : WordColourStateRelation
      (wordGraphColouringAt allocation.colouring) source target)
    (hprogram : WordVarStraightLine width
      (wordSsaRenameFunctionWithEntry parameters program).2.snd) :
    ∃ sourcePrime targetPrime,
      evalWordProg source
          (wordSsaRenameFunctionWithEntry parameters program).2.snd =
        some sourcePrime ∧
      evalWordProg target coloured = some targetPrime ∧
      WordColourStateRelation (wordGraphColouringAt allocation.colouring)
        sourcePrime targetPrime := by
  simp [wordAllocateGraphFunctionWithEntry] at halloc
  rcases halloc with ⟨a, _, _, _, ha, hcolour⟩
  have hvalid : wordColourValid (wordGraphColouringAt a.colouring) := by
    simpa [ha] using valid
  have hinjective : Function.Injective
      (wordGraphColouringAt a.colouring) := by
    simpa [ha] using injective
  have hzero : wordGraphColouringAt a.colouring 0 = 0 := by
    simpa [ha] using colourZero
  have hscratch : ∀ name, name < 31 →
      wordGraphColouringAt a.colouring name ≠ 31 := by
    simpa [ha] using colourNoScratch
  have hrelationA : WordColourStateRelation
      (wordGraphColouringAt a.colouring) source target := by
    simpa [ha] using hrelation
  have hresult := evalWordProg_wordVarStraightLine_applyColour
    (wordGraphColouringAt a.colouring) hvalid hinjective hzero
    hscratch source target hrelationA
    (wordSsaRenameFunctionWithEntry parameters program).2.snd hprogram
  rw [hcolour] at hresult
  simpa [ha] using hresult

/-! The same machine boundary, lifted to the full-SSA graph allocator.  The
    allocator result remains explicit, while its colored output is connected
    to the backend grammar using the renamed full-SSA body witness. -/

theorem wordAllocateGraphFunctionWithEntry_riscv_straightLine_simulation
    [NeZero width]
    (parameters : List Nat) (program : WordProg (Word width))
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (coloured : WordProg (Word width))
    (halloc : wordAllocateGraphFunctionWithEntry parameters program fixedSources
      colours stackStart =
      some (state, renamedParameters, allocation, coloured))
    (valid : wordColourValid (wordGraphColouringAt allocation.colouring))
    (injective : Function.Injective
      (wordGraphColouringAt allocation.colouring))
    (colourZero : wordGraphColouringAt allocation.colouring 0 = 0)
    (colourNoScratch : ∀ name, name < 31 →
      wordGraphColouringAt allocation.colouring name ≠ 31)
    (source target : State width)
    (hrelation : WordColourStateRelation
      (wordGraphColouringAt allocation.colouring) source target)
    (hprogram : WordVarStraightLine width
      (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    (code : List (Instruction width))
    (hcompile : wordProgToRiscV coloured = some code) :
    ∃ source' target',
      evalWordProg source
          (wordSsaRenameFunctionWithEntry parameters program).2.snd =
        some source' ∧
      executeInstructions target code = target' ∧
      WordColourStateRelation (wordGraphColouringAt allocation.colouring)
        source' target' := by
  have hsimulation := wordAllocateGraphFunctionWithEntry_straightLine_simulation
    parameters program fixedSources colours stackStart state renamedParameters
    allocation coloured halloc valid injective colourZero colourNoScratch source target
    hrelation hprogram
  rcases hsimulation with
    ⟨source', target', hsource, htarget, htargetRelation⟩
  have halloc' := halloc
  simp [wordAllocateGraphFunctionWithEntry] at halloc'
  rcases halloc' with ⟨actualAllocation, _, _, _, hallocation, hcolour⟩
  have htargetStraight' := wordVarStraightLine_to_wordRiscVStraightLine
    (wordGraphColouringAt actualAllocation.colouring)
    (wordSsaRenameFunctionWithEntry parameters program).2.snd hprogram
  rw [hcolour] at htargetStraight'
  have htargetStraight : WordRiscVStraightLine coloured := by
    simpa [hallocation] using htargetStraight'
  have hmachine := wordProgToRiscV_sound_of_straightLine target coloured
    htargetStraight code hcompile
  have htargetEq : target' = executeInstructions target code :=
    Option.some.inj (htarget.symm.trans hmachine)
  subst target'
  exact ⟨source', executeInstructions target code, hsource, rfl, htargetRelation⟩

theorem wordColourStateRelation_evalWordCondition [NeZero width]
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (source target : State width)
    (hrelation : WordColourStateRelation colour source target)
    (operator : Cmp) (condition : Nat)
    (rightValue : WordRegImm (Word width))
    (hcondition : condition < 32)
    (hright : ∀ name, rightValue = .reg name → name < 32) :
    evalWordCondition source operator condition rightValue =
      evalWordCondition target operator (colour condition)
        (wordApplyColourRegImm colour rightValue) := by
  cases rightValue with
  | imm value =>
      have hcondition' : colour condition < 32 := valid condition hcondition
      have hconditionValue := hrelation.register condition hcondition hcondition'
      cases operator <;>
        simp [evalWordCondition, wordApplyColourRegImm, registerOfNat,
          hcondition, hcondition', hconditionValue]
  | reg right =>
      have hright' : right < 32 := hright right rfl
      have hcondition' : colour condition < 32 := valid condition hcondition
      have hrightColour : colour right < 32 := valid right hright'
      have hleftValue := hrelation.register condition hcondition
        (valid condition hcondition)
      have hrightValue := hrelation.register right hright'
        (valid right hright')
      cases operator <;>
        simp [evalWordCondition, wordApplyColourRegImm, registerOfNat,
          hcondition, hright', hcondition', hrightColour, hleftValue,
          hrightValue]

theorem evalWordProg_ite_applyColour [NeZero width]
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (colourNoScratch : ∀ name, name < 31 → colour name ≠ 31)
    (source target : State width)
    (hrelation : WordColourStateRelation colour source target)
    (operator : Cmp) (condition : Nat)
    (rightValue : WordRegImm (Word width))
    (choose : Bool)
    (hcondition : condition < 32)
    (hright : ∀ name, rightValue = .reg name → name < 32)
    (hchoose : evalWordCondition source operator condition rightValue =
      some choose)
    (thenBranch elseBranch : WordProg (Word width))
    (hthen : WordVarStraightLine width thenBranch)
    (helse : WordVarStraightLine width elseBranch) :
    ∃ source' target',
      evalWordProg source
          (.ite operator condition rightValue thenBranch elseBranch) =
        some source' ∧
      evalWordProg target
          (wordApplyColour colour
            (.ite operator condition rightValue thenBranch elseBranch)) =
        some target' ∧
      WordColourStateRelation colour source' target' := by
  have hcondition' := wordColourStateRelation_evalWordCondition colour valid
    source target hrelation operator condition rightValue hcondition hright
  rw [hchoose] at hcondition'
  have hcondition'' := hcondition'.symm
  cases choose with
  | false =>
      rcases evalWordProg_wordVarStraightLine_applyColour colour valid
        injective colourZero colourNoScratch source target hrelation elseBranch helse with
        ⟨source', target', hsource, htarget, hrelation'⟩
      refine ⟨source', target', ?_, ?_, hrelation'⟩
      · simp [evalWordProg, hchoose, hsource]
      · simp [evalWordProg, wordApplyColour, hcondition'', htarget]
  | true =>
      rcases evalWordProg_wordVarStraightLine_applyColour colour valid
        injective colourZero colourNoScratch source target hrelation thenBranch hthen with
        ⟨source', target', hsource, htarget, hrelation'⟩
      refine ⟨source', target', ?_, ?_, hrelation'⟩
      · simp [evalWordProg, hchoose, hsource]
      · simp [evalWordProg, wordApplyColour, hcondition'', htarget]

theorem evalWordFunction_wordVarStraightLine_eq_evalWordProg [NeZero width]
    (state : State width) (program : WordProg (Word width))
    (hprogram : WordVarStraightLine width program) :
    evalWordFunction state program =
      (evalWordProg state program).map (fun state => (state, [])) := by
  induction hprogram generalizing state with
  | skip => simp [evalWordFunction, evalWordProg]
  | moveOne name sourceName hname hsource hname31 hsource31 hne =>
      simp [evalWordFunction, evalWordProg, Function.comp_def]
  | moveTwo destinationOne sourceOne destinationTwo sourceTwo
      hdestinationOne hsourceOne hdestinationTwo hsourceTwo
      hdestinationOne31 hsourceOne31 hdestinationTwo31 hsourceTwo31
      hdestinations hsourceOneDestinationOne hsourceOneDestinationTwo
      hsourceTwoDestinationOne hsourceTwoDestinationTwo =>
      simp [evalWordFunction, evalWordProg, Function.comp_def]
  | assign name sourceName hname hsource =>
      simp [evalWordFunction, evalWordProg, Function.comp_def]
  | assignConst name value hname =>
      simp [evalWordFunction, evalWordProg, Function.comp_def]
  | assignBinary operator name left right hname hleft hright =>
      simp [evalWordFunction, evalWordProg, Function.comp_def]
  | assignImmediate operator name source value hname hsource =>
      simp [evalWordFunction, evalWordProg, Function.comp_def]
  | assignShift operator name left right hoperator hname hleft hright =>
      simp [evalWordFunction, evalWordProg, Function.comp_def]
  | assignShiftImmediate operator name left amount hoperator hname hleft =>
      simp [evalWordFunction, evalWordProg, Function.comp_def]
  | @seq first second hfirst hsecond ihFirst ihSecond =>
      simp only [evalWordFunction, evalWordProg]
      rw [ihFirst state]
      cases hfirstEval : evalWordProg state first with
      | none => simp
      | some firstState =>
          simp [ihSecond firstState]
          cases hsecondEval : evalWordProg firstState second with
          | none => simp
          | some secondState => simp

theorem wordVarStraightLine_applyColour
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour)
    (colourNoScratch : ∀ name, name < 31 → colour name ≠ 31)
    {program : WordProg (Word width)}
    (hprogram : WordVarStraightLine width program) :
    WordVarStraightLine width (wordApplyColour colour program) := by
  induction hprogram with
  | skip => simp [wordApplyColour]; exact .skip
  | moveOne name sourceName hname hsource hname31 hsource31 hne =>
      have hnameLT31 : name < 31 := by omega
      have hsourceLT31 : sourceName < 31 := by omega
      simpa [wordApplyColour] using
        (.moveOne (colour name) (colour sourceName)
          (valid name hname) (valid sourceName hsource)
          (colourNoScratch name hnameLT31)
          (colourNoScratch sourceName hsourceLT31)
          (by intro h; apply hne; exact injective h))
  | moveTwo destinationOne sourceOne destinationTwo sourceTwo
      hdestinationOne hsourceOne hdestinationTwo hsourceTwo
      hdestinationOne31 hsourceOne31 hdestinationTwo31 hsourceTwo31
      hdestinations hsourceOneDestinationOne hsourceOneDestinationTwo
      hsourceTwoDestinationOne hsourceTwoDestinationTwo =>
      have hdestinationOneLT31 : destinationOne < 31 := by omega
      have hsourceOneLT31 : sourceOne < 31 := by omega
      have hdestinationTwoLT31 : destinationTwo < 31 := by omega
      have hsourceTwoLT31 : sourceTwo < 31 := by omega
      simpa [wordApplyColour] using
        (.moveTwo (colour destinationOne) (colour sourceOne)
          (colour destinationTwo) (colour sourceTwo)
          (valid destinationOne hdestinationOne) (valid sourceOne hsourceOne)
          (valid destinationTwo hdestinationTwo) (valid sourceTwo hsourceTwo)
          (colourNoScratch destinationOne hdestinationOneLT31)
          (colourNoScratch sourceOne hsourceOneLT31)
          (colourNoScratch destinationTwo hdestinationTwoLT31)
          (colourNoScratch sourceTwo hsourceTwoLT31)
          (by intro h; apply hdestinations; exact injective h)
          (by intro h; apply hsourceOneDestinationOne; exact injective h)
          (by intro h; apply hsourceOneDestinationTwo; exact injective h)
          (by intro h; apply hsourceTwoDestinationOne; exact injective h)
          (by intro h; apply hsourceTwoDestinationTwo; exact injective h))
  | assign name sourceName hname hsource =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assign (colour name) (colour sourceName)
          (valid name hname) (valid sourceName hsource))
  | assignConst name value hname =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assignConst (colour name) value (valid name hname))
  | assignBinary operator name left right hname hleft hright =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assignBinary operator (colour name) (colour left) (colour right)
          (valid name hname) (valid left hleft) (valid right hright))
  | assignImmediate operator name sourceName value hname hsource =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assignImmediate operator (colour name) (colour sourceName) value
          (valid name hname) (valid sourceName hsource))
  | assignShift operator name left right hoperator hname hleft hright =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assignShift operator (colour name) (colour left) (colour right)
          hoperator (valid name hname) (valid left hleft) (valid right hright))
  | assignShiftImmediate operator name left amount hoperator hname hleft =>
      simpa [wordApplyColour, wordApplyColourExp] using
        (.assignShiftImmediate operator (colour name) (colour left) amount
          hoperator (valid name hname) (valid left hleft))
  | @seq first second hfirst hsecond ihFirst ihSecond =>
      simpa [wordApplyColour] using .seq ihFirst ihSecond

theorem evalWordFunction_wordVarStraightLine_applyColour [NeZero width]
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (colourNoScratch : ∀ name, name < 31 → colour name ≠ 31)
    (source target : State width)
    (hrelation : WordColourStateRelation colour source target)
    (program : WordProg (Word width))
    (hprogram : WordVarStraightLine width program) :
    ∃ source' target',
      evalWordFunction source program = some (source', []) ∧
      evalWordFunction target (wordApplyColour colour program) =
        some (target', []) ∧
      WordColourStateRelation colour source' target' := by
  rcases evalWordProg_wordVarStraightLine_applyColour colour valid injective
    colourZero colourNoScratch source target hrelation program hprogram with
    ⟨source', target', hsource, htarget, hrelation'⟩
  refine ⟨source', target', ?_, ?_, hrelation'⟩
  · rw [evalWordFunction_wordVarStraightLine_eq_evalWordProg source program
      hprogram, hsource]
    rfl
  · rw [evalWordFunction_wordVarStraightLine_eq_evalWordProg target
      (wordApplyColour colour program) ?_]
    · rw [htarget]
      rfl
    · exact wordVarStraightLine_applyColour colour valid injective
        colourNoScratch hprogram

/-! Compose the straight-line body theorem with the ABI return boundary.  This
    is the function-shaped contract consumed by full-SSA call proofs: the
    coloured body preserves the state relation and its renamed return reads
    produce exactly the same values. -/

theorem evalWordFunction_wordVarStraightLine_return_applyColour [NeZero width]
    (colour : Nat → Nat) (valid : wordColourValid colour)
    (injective : Function.Injective colour) (colourZero : colour 0 = 0)
    (colourNoScratch : ∀ name, name < 31 → colour name ≠ 31)
    (source target : State width)
    (hrelation : WordColourStateRelation colour source target)
    (program : WordProg (Word width))
    (hprogram : WordVarStraightLine width program)
    (label : Nat) (values : List Nat)
    (hvalues : ∀ name, name ∈ values → name < 32) :
    ∃ source' target' returnedValues,
      evalWordFunction source (.seq program (.return label values)) =
        some (source', returnedValues) ∧
      evalWordFunction target
          (.seq (wordApplyColour colour program)
            (.return label (values.map colour))) =
        some (target', returnedValues) ∧
      WordColourStateRelation colour source' target' := by
  rcases evalWordFunction_wordVarStraightLine_applyColour colour valid injective
    colourZero colourNoScratch source target hrelation program hprogram with
    ⟨source', target', hsource, htarget, hrelation'⟩
  have hreturns :
      values.mapM (fun name => do
        let register ← RiscV.registerOfNat name
        pure (RiscV.readRegister source' register)) =
      (values.map colour).mapM (fun name => do
        let register ← RiscV.registerOfNat name
        pure (RiscV.readRegister target' register)) := by
    induction values with
    | nil => rfl
    | cons name values ih =>
        simp only [List.map, List.mapM_cons]
        have hname := hvalues name (by simp)
        have hcolour : colour name < 32 := valid name hname
        have hregister := hrelation'.register name hname hcolour
        have hhead :
            (do
              let register ← RiscV.registerOfNat name
              pure (RiscV.readRegister source' register)) =
            (do
              let register ← RiscV.registerOfNat (colour name)
              pure (RiscV.readRegister target' register)) := by
          simp [RiscV.registerOfNat, hname, hcolour, hregister]
        have htail : ∀ name, name ∈ values → name < 32 := by
          intro name hname
          exact hvalues name (by simp [hname])
        rw [hhead, ih htail]
  have hmapSome : ∀ (state : State width) (names : List Nat),
      (∀ name, name ∈ names → name < 32) →
      ∃ result, List.mapM (fun name => do
        let register ← RiscV.registerOfNat name
        pure (RiscV.readRegister state register)) names = some result := by
    intro state names
    induction names with
    | nil =>
        intro _
        exact ⟨[], rfl⟩
    | cons name names ih =>
        intro hnames
        have hname : name < 32 := hnames name (by simp)
        have htail : ∀ name, name ∈ names → name < 32 := by
          intro name hname'
          exact hnames name (by simp [hname'])
        have hregister : RiscV.registerOfNat name = some ⟨name, hname⟩ := by
          simp [RiscV.registerOfNat, hname]
        rcases ih htail with ⟨result, hresult⟩
        refine ⟨RiscV.readRegister state ⟨name, hname⟩ :: result, ?_⟩
        simp only [List.mapM_cons, hregister]
        rw [hresult]
        rfl
  rcases hmapSome source' values hvalues with
    ⟨sourceValues, hsourceValues⟩
  have hcolouredValues : ∀ name, name ∈ values.map colour → name < 32 := by
    intro name hname
    rcases List.mem_map.mp hname with ⟨sourceName, hsourceName, rfl⟩
    exact valid sourceName (hvalues sourceName hsourceName)
  rcases hmapSome target' (values.map colour) hcolouredValues with
    ⟨targetValues, htargetValues⟩
  have hvaluesEq : sourceValues = targetValues := by
    rw [hsourceValues, htargetValues] at hreturns
    exact Option.some.inj hreturns
  subst targetValues
  refine ⟨source', target', sourceValues, ?_, ?_⟩
  · simp only [evalWordFunction]
    rw [hsource]
    have hsourceValues' :
        values.mapM (fun name =>
          (RiscV.registerOfNat name).bind (fun register =>
            some (RiscV.readRegister source' register))) =
          some sourceValues := by
      simpa [Option.map, Option.bind] using hsourceValues
    simp [hsourceValues']
  · refine ⟨?_, hrelation'⟩
    simp only [evalWordFunction]
    rw [htarget]
    have htargetValues' :
        (values.map colour).mapM (fun name =>
          (RiscV.registerOfNat name).bind (fun register =>
            some (RiscV.readRegister target' register))) =
          some sourceValues := by
      simpa [Option.map, Option.bind] using htargetValues
    have htargetValues'' :
        List.mapM ((fun name =>
          (RiscV.registerOfNat name).bind (fun register =>
            some (RiscV.readRegister target' register))) ∘ colour) values =
          some sourceValues := by
      simpa [Function.comp_def, List.mapM_map] using htargetValues'
    simp [htargetValues'']

/-! Lift the function-shaped return contract through the executable graph
    allocator.  The allocator result is kept explicit so callers can use the
    same theorem with a concrete allocation witness or with a downstream
    allocator driver. -/

theorem wordAllocateGraphFunctionWithEntry_return_simulation [NeZero width]
    (parameters : List Nat) (program : WordProg (Word width))
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation)
    (colouredProgram : WordProg (Word width))
    (halloc : wordAllocateGraphFunctionWithEntry parameters program fixedSources
      colours stackStart =
      some (state, renamedParameters, allocation, colouredProgram))
    (valid : wordColourValid (wordGraphColouringAt allocation.colouring))
    (injective : Function.Injective
      (wordGraphColouringAt allocation.colouring))
    (colourZero : wordGraphColouringAt allocation.colouring 0 = 0)
    (colourNoScratch : ∀ name, name < 31 →
      wordGraphColouringAt allocation.colouring name ≠ 31)
    (source target : State width)
    (hrelation : WordColourStateRelation
      (wordGraphColouringAt allocation.colouring) source target)
    (hprogram : WordVarStraightLine width
      (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    (label : Nat) (values : List Nat)
    (hvalues : ∀ name, name ∈ values → name < 32) :
    ∃ source' target' returnedValues,
      evalWordFunction source
          (.seq (wordSsaRenameFunctionWithEntry parameters program).2.snd
            (.return label values)) =
        some (source', returnedValues) ∧
      evalWordFunction target
          (.seq colouredProgram (.return label (values.map
            (wordGraphColouringAt allocation.colouring)))) =
        some (target', returnedValues) ∧
      WordColourStateRelation (wordGraphColouringAt allocation.colouring)
        source' target' := by
  simp [wordAllocateGraphFunctionWithEntry] at halloc
  rcases halloc with ⟨a, _, _, _, ha, hcolour⟩
  have hvalid : wordColourValid (wordGraphColouringAt a.colouring) := by
    simpa [ha] using valid
  have hinjective : Function.Injective
      (wordGraphColouringAt a.colouring) := by
    simpa [ha] using injective
  have hzero : wordGraphColouringAt a.colouring 0 = 0 := by
    simpa [ha] using colourZero
  have hscratch : ∀ name, name < 31 →
      wordGraphColouringAt a.colouring name ≠ 31 := by
    simpa [ha] using colourNoScratch
  have hrelationA : WordColourStateRelation
      (wordGraphColouringAt a.colouring) source target := by
    simpa [ha] using hrelation
  have hresult := evalWordFunction_wordVarStraightLine_return_applyColour
    (wordGraphColouringAt a.colouring) hvalid hinjective hzero hscratch
    source target hrelationA
    (wordSsaRenameFunctionWithEntry parameters program).2.snd hprogram
    label values hvalues
  rw [hcolour] at hresult
  simpa [ha] using hresult

/-! Lift the executable full-SSA allocator contract through the backend's
    function-shaped return boundary.  This is the first theorem that ties the
    allocator's coloured body to the instruction stream and the returned
    register values consumed by a caller. -/

theorem wordAllocateGraphFunctionWithEntry_riscv_return_simulation
    [NeZero width]
    (context : WordCallContext width)
    (parameters : List Nat) (program : WordProg (Word width))
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (coloured : WordProg (Word width))
    (halloc : wordAllocateGraphFunctionWithEntry parameters program fixedSources
      colours stackStart =
      some (state, renamedParameters, allocation, coloured))
    (valid : wordColourValid (wordGraphColouringAt allocation.colouring))
    (injective : Function.Injective
      (wordGraphColouringAt allocation.colouring))
    (colourZero : wordGraphColouringAt allocation.colouring 0 = 0)
    (colourNoScratch : ∀ name, name < 31 →
      wordGraphColouringAt allocation.colouring name ≠ 31)
    (source target : State width)
    (hrelation : WordColourStateRelation
      (wordGraphColouringAt allocation.colouring) source target)
    (hprogram : WordVarStraightLine width
      (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    (store : Nat) (values : List Nat)
    (hvalues : ∀ name, name ∈ values → name < 32)
    (code : List (Instruction width))
    (returns : List (Fin 32))
    (hcompile : wordFunctionToRiscVWithCalls context coloured =
      some (code, []))
    (hreturnCompile : wordFunctionToRiscVWithCalls context
      ((.return store (values.map
        (wordGraphColouringAt allocation.colouring))) : WordProg (Word width)) =
      some ([], returns)) :
    ∃ source' returnedValues,
      evalWordFunction source
          (.seq (wordSsaRenameFunctionWithEntry parameters program).2.snd
            (.return store values)) =
        some (source', returnedValues) ∧
      evalWordFunction target
          (.seq coloured (.return store (values.map
            (wordGraphColouringAt allocation.colouring)))) =
        some (executeInstructions target code, returnedValues) ∧
      WordColourStateRelation (wordGraphColouringAt allocation.colouring)
        source' (executeInstructions target code) := by
  have halloc' := halloc
  simp [wordAllocateGraphFunctionWithEntry] at halloc'
  rcases halloc' with ⟨actualAllocation, _, _, _, hallocation, hcolour⟩
  have hvalid : wordColourValid (wordGraphColouringAt actualAllocation.colouring) := by
    simpa [hallocation] using valid
  have hinjective : Function.Injective
      (wordGraphColouringAt actualAllocation.colouring) := by
    simpa [hallocation] using injective
  have hzero : wordGraphColouringAt actualAllocation.colouring 0 = 0 := by
    simpa [hallocation] using colourZero
  have hscratch : ∀ name, name < 31 →
      wordGraphColouringAt actualAllocation.colouring name ≠ 31 := by
    simpa [hallocation] using colourNoScratch
  have hrelationA : WordColourStateRelation
      (wordGraphColouringAt actualAllocation.colouring) source target := by
    simpa [hallocation] using hrelation
  have hsimulation := evalWordFunction_wordVarStraightLine_return_applyColour
    (wordGraphColouringAt actualAllocation.colouring) hvalid hinjective hzero
    hscratch source target hrelationA
    (wordSsaRenameFunctionWithEntry parameters program).2.snd hprogram
    store values hvalues
  rw [hcolour] at hsimulation
  have hsimulation' :
      ∃ source' target' returnedValues,
        evalWordFunction source
            (.seq (wordSsaRenameFunctionWithEntry parameters program).2.snd
              (.return store values)) =
          some (source', returnedValues) ∧
        evalWordFunction target
            (.seq coloured (.return store (values.map
              (wordGraphColouringAt allocation.colouring)))) =
          some (target', returnedValues) ∧
        WordColourStateRelation (wordGraphColouringAt allocation.colouring)
          source' target' := by
    simpa [hallocation] using hsimulation
  rcases hsimulation' with
    ⟨source', target', returnedValues, hsource, htarget, htargetRelation⟩
  have htargetStraight' := wordVarStraightLine_to_wordRiscVStraightLine
    (wordGraphColouringAt actualAllocation.colouring)
    (wordSsaRenameFunctionWithEntry parameters program).2.snd hprogram
  rw [hcolour] at htargetStraight'
  have htargetStraight : WordRiscVStraightLine coloured := by
    simpa [hallocation] using htargetStraight'
  have hmachine := wordFunctionToRiscVWithCalls_seq_return_sound
    context target coloured htargetStraight store
    (values.map (wordGraphColouringAt allocation.colouring)) code returns
    hcompile hreturnCompile
  have htargetEq :
      some (target', returnedValues) =
        Option.map (fun returned =>
          (executeInstructions target code, returned))
          ((values.map (wordGraphColouringAt allocation.colouring)).mapM
            (fun name => do
              let register ← registerOfNat name
              pure (readRegister (executeInstructions target code) register))) := by
    rw [← htarget]
    exact hmachine.2
  have htargetState : target' = executeInstructions target code := by
    generalize hread : ((values.map (wordGraphColouringAt allocation.colouring)).mapM
        (fun name => do
          let register ← registerOfNat name
          pure (readRegister (executeInstructions target code) register))) =
      readValues at htargetEq
    cases readValues with
    | none => simp at htargetEq
    | some readValues =>
        simp at htargetEq
        exact htargetEq.1
  subst target'
  exact ⟨source', returnedValues, hsource, htarget, htargetRelation⟩

/-! The same allocator boundary is available to the FFI-aware RISC-V
    selector.  On a straight-line colored body the selector intentionally
    agrees with the ordinary one, so this theorem exposes that fact without
    forcing callers to erase the service environment by hand. -/

theorem wordAllocateGraphFunctionWithEntry_riscv_ffi_return_simulation
    [NeZero width]
    (context : WordCallFfiContext width)
    (parameters : List Nat) (program : WordProg (Word width))
    (fixedSources : List Nat) (colours stackStart : Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (allocation : WordGraphAllocation) (coloured : WordProg (Word width))
    (halloc : wordAllocateGraphFunctionWithEntry parameters program fixedSources
      colours stackStart =
      some (state, renamedParameters, allocation, coloured))
    (valid : wordColourValid (wordGraphColouringAt allocation.colouring))
    (injective : Function.Injective
      (wordGraphColouringAt allocation.colouring))
    (colourZero : wordGraphColouringAt allocation.colouring 0 = 0)
    (colourNoScratch : ∀ name, name < 31 →
      wordGraphColouringAt allocation.colouring name ≠ 31)
    (source target : State width)
    (hrelation : WordColourStateRelation
      (wordGraphColouringAt allocation.colouring) source target)
    (hprogram : WordVarStraightLine width
      (wordSsaRenameFunctionWithEntry parameters program).2.snd)
    (store : Nat) (values : List Nat)
    (hvalues : ∀ name, name ∈ values → name < 32)
    (code : List (Instruction width))
    (returns : List (Fin 32))
    (hcompile : wordFunctionToRiscVWithCallsAndFfi context coloured =
      some (code, []))
    (hreturnCompile : wordFunctionToRiscVWithCallsAndFfi context
      ((.return store (values.map
        (wordGraphColouringAt allocation.colouring))) : WordProg (Word width)) =
      some ([], returns)) :
    ∃ source' returnedValues,
      evalWordFunction source
          (.seq (wordSsaRenameFunctionWithEntry parameters program).2.snd
            (.return store values)) =
        some (source', returnedValues) ∧
      evalWordFunction target
          (.seq coloured (.return store (values.map
            (wordGraphColouringAt allocation.colouring)))) =
        some (executeInstructions target code, returnedValues) ∧
      WordColourStateRelation (wordGraphColouringAt allocation.colouring)
        source' (executeInstructions target code) := by
  have halloc' := halloc
  simp [wordAllocateGraphFunctionWithEntry] at halloc'
  rcases halloc' with ⟨actualAllocation, _, _, _, hallocation, hcolour⟩
  have htargetStraight' := wordVarStraightLine_to_wordRiscVStraightLine
    (wordGraphColouringAt actualAllocation.colouring)
    (wordSsaRenameFunctionWithEntry parameters program).2.snd hprogram
  rw [hcolour] at htargetStraight'
  have htargetStraight : WordRiscVStraightLine coloured := by
    simpa [hallocation] using htargetStraight'
  have hcompileOrdinary : wordFunctionToRiscVWithCalls
      { targets := context.targets } coloured = some (code, []) := by
    rw [← wordFunctionToRiscVWithCallsAndFfi_agrees_straightLine
      context coloured htargetStraight]
    exact hcompile
  have hreturnOrdinary : wordFunctionToRiscVWithCalls
      { targets := context.targets }
      ((.return store (values.map
        (wordGraphColouringAt allocation.colouring))) : WordProg (Word width)) =
      some ([], returns) := by
    cases hmap : (values.map (wordGraphColouringAt allocation.colouring)).mapM
        registerOfNat with
    | none =>
        simp [wordFunctionToRiscVWithCallsAndFfi,
          wordFunctionToRiscVWithCalls, hmap] at hreturnCompile
    | some registers =>
        simpa [wordFunctionToRiscVWithCallsAndFfi,
          wordFunctionToRiscVWithCalls, hmap] using hreturnCompile
  exact wordAllocateGraphFunctionWithEntry_riscv_return_simulation
    { targets := context.targets } parameters program fixedSources colours stackStart
    state renamedParameters allocation coloured halloc valid injective colourZero
    colourNoScratch source target hrelation hprogram store values hvalues code returns
    hcompileOrdinary hreturnOrdinary

/-! A call-level colouring contract for the handler-aware Word evaluator.  It
keeps the source and target body proofs explicit, so the theorem composes with
straight-line, loop, and FFI body simulations without unfolding those bodies
at every caller.  As in the evaluator, only the callee memory and machine
mode escape the call frame; caller registers remain related by the incoming
colouring relation. -/

theorem evalWordCallWithHandlersAndFfi_return_applyColour_general [NeZero width]
    (colour : Nat → Nat)
    (sourceFunctions targetFunctions : List
      (Nat × List Nat × WordProg (Word width)))
    (sourceHandler targetHandler : FunName → Word width → Word width →
      Word width → Word width → State width → Option (State width))
    (fuel functionLabel : Nat) (parameters : List Nat)
    (arguments : List Nat) (colouredArguments : List Nat)
    (argumentValues : List (Word width))
    (sourceBody targetBody : WordProg (Word width))
    (sourceState targetState : State width)
    (sourceCallee targetCallee : State width)
    (sourceBodyState targetBodyState : State width)
    (sourceValues targetValues : List (Word width))
    (hlookupSource : lookupWordFunction functionLabel sourceFunctions =
      some (parameters, sourceBody))
    (hlookupTarget : lookupWordFunction functionLabel targetFunctions =
      some (parameters.map colour, targetBody))
    (hargumentsSource : readWordRegisters sourceState arguments =
      some argumentValues)
    (hargumentsTarget : readWordRegisters targetState colouredArguments =
      some argumentValues)
    (hbindSource : bindWordRegisters sourceState parameters argumentValues =
      some sourceCallee)
    (hbindTarget : bindWordRegisters targetState (parameters.map colour)
      argumentValues = some targetCallee)
    (hbodySource : evalWordFunctionWithHandlersAndFfi sourceFunctions
      sourceHandler fuel sourceCallee sourceBody =
      some (.returned sourceBodyState sourceValues))
    (hbodyTarget : evalWordFunctionWithHandlersAndFfi targetFunctions
      targetHandler fuel targetCallee targetBody =
      some (.returned targetBodyState targetValues))
    (hcallerRelation : WordColourStateRelation colour sourceState targetState)
    (hbodyRelation : WordColourStateRelation colour
      sourceBodyState targetBodyState)
    (hvalues : targetValues = sourceValues) :
    evalWordCallWithHandlersAndFfi sourceFunctions sourceHandler (fuel + 1)
      sourceState none (some functionLabel) arguments none =
        some (.returned
          { sourceState with
            memory := sourceBodyState.memory
            privilege := sourceBodyState.privilege
            mode := sourceBodyState.mode }
          sourceValues) ∧
    evalWordCallWithHandlersAndFfi targetFunctions targetHandler (fuel + 1)
      targetState none (some functionLabel) colouredArguments none =
        some (.returned
          { targetState with
            memory := targetBodyState.memory
            privilege := targetBodyState.privilege
            mode := targetBodyState.mode }
          targetValues) ∧
    WordColourStateRelation colour
      { sourceState with
        memory := sourceBodyState.memory
        privilege := sourceBodyState.privilege
        mode := sourceBodyState.mode }
      { targetState with
        memory := targetBodyState.memory
        privilege := targetBodyState.privilege
        mode := targetBodyState.mode } ∧
    targetValues = sourceValues := by
  have hsourceResult := evalWordCallWithHandlersAndFfi_return_of_eval
    sourceFunctions sourceHandler fuel sourceState sourceCallee sourceBodyState
    functionLabel parameters arguments sourceBody argumentValues sourceValues
    hlookupSource hargumentsSource hbindSource hbodySource
  have htargetResult := evalWordCallWithHandlersAndFfi_return_of_eval
    targetFunctions targetHandler fuel targetState targetCallee targetBodyState
    functionLabel (parameters.map colour) colouredArguments targetBody argumentValues
    targetValues hlookupTarget hargumentsTarget hbindTarget hbodyTarget
  have hfinal : WordColourStateRelation colour
      { sourceState with
        memory := sourceBodyState.memory
        privilege := sourceBodyState.privilege
        mode := sourceBodyState.mode }
      { targetState with
        memory := targetBodyState.memory
        privilege := targetBodyState.privilege
        mode := targetBodyState.mode } := by
    constructor
    · exact hcallerRelation.pc
    · exact hbodyRelation.memory
    · exact hbodyRelation.privilege
    · exact hbodyRelation.mode
    · intro name hname hcolour
      exact hcallerRelation.register name hname hcolour
  exact ⟨hsourceResult, htargetResult, hfinal, hvalues⟩

/-! The raised-call counterpart carries an exception through the coloured
    handler register before running the two related handler bodies.  Keeping
    the handler-entry relation explicit makes this usable for nested caught
    calls and for handlers that contain FFI leaves. -/

theorem evalWordCallWithHandlersAndFfi_raiseHandler_applyColour_general
    [NeZero width]
    (colour : Nat → Nat)
    (sourceFunctions targetFunctions : List
      (Nat × List Nat × WordProg (Word width)))
    (sourceHandler targetHandler : FunName → Word width → Word width →
      Word width → Word width → State width → Option (State width))
    (fuel functionLabel : Nat) (parameters : List Nat)
    (arguments colouredArguments : List Nat)
    (argumentValues : List (Word width))
    (sourceBody targetBody : WordProg (Word width))
    (sourceState targetState : State width)
    (sourceCallee targetCallee : State width)
    (sourceBodyState targetBodyState : State width)
    (sourceException targetException handlerName : Nat)
    (handlerLabel entryLabel : Nat)
    (sourceHandlerBody targetHandlerBody : WordProg (Word width))
    (sourceHandlerState targetHandlerState : State width)
    (sourceValues targetValues : List (Word width))
    (valid : wordColourValid colour)
    (injective : Function.Injective colour)
    (colourZero : colour 0 = 0)
    (hlookupSource : lookupWordFunction functionLabel sourceFunctions =
      some (parameters, sourceBody))
    (hlookupTarget : lookupWordFunction functionLabel targetFunctions =
      some (parameters.map colour, targetBody))
    (hargumentsSource : readWordRegisters sourceState arguments =
      some argumentValues)
    (hargumentsTarget : readWordRegisters targetState colouredArguments =
      some argumentValues)
    (hbindSource : bindWordRegisters sourceState parameters argumentValues =
      some sourceCallee)
    (hbindTarget : bindWordRegisters targetState (parameters.map colour)
      argumentValues = some targetCallee)
    (hbodySource : evalWordFunctionWithHandlersAndFfi sourceFunctions
      sourceHandler fuel sourceCallee sourceBody =
      some (.raised sourceBodyState sourceException))
    (hbodyTarget : evalWordFunctionWithHandlersAndFfi targetFunctions
      targetHandler fuel targetCallee targetBody =
      some (.raised targetBodyState targetException))
    (hsourceHandlerName : handlerName < 32)
    (hsourceHandlerRegister : registerOfNat handlerName =
      some ⟨handlerName, hsourceHandlerName⟩)
    (htargetHandlerRegister : registerOfNat (colour handlerName) =
      some ⟨colour handlerName, valid handlerName hsourceHandlerName⟩)
    (hhandlerSource : evalWordFunctionWithHandlersAndFfi sourceFunctions
      sourceHandler fuel
      (writeRegister
        { sourceState with
          memory := sourceBodyState.memory
          privilege := sourceBodyState.privilege
          mode := sourceBodyState.mode }
        ⟨handlerName, hsourceHandlerName⟩
        (BitVec.ofNat width sourceException)) sourceHandlerBody =
      some (.returned sourceHandlerState sourceValues))
    (hhandlerTarget : evalWordFunctionWithHandlersAndFfi targetFunctions
      targetHandler fuel
      (writeRegister
        { targetState with
          memory := targetBodyState.memory
          privilege := targetBodyState.privilege
          mode := targetBodyState.mode }
        ⟨colour handlerName, valid handlerName hsourceHandlerName⟩
        (BitVec.ofNat width targetException)) targetHandlerBody =
      some (.returned targetHandlerState targetValues))
    (hcallerRelation : WordColourStateRelation colour sourceState targetState)
    (hbodyRelation : WordColourStateRelation colour
      sourceBodyState targetBodyState)
    (hhandlerRelation : WordColourStateRelation colour
      sourceHandlerState targetHandlerState)
    (hexception : targetException = sourceException)
    (hvalues : targetValues = sourceValues) :
    evalWordCallWithHandlersAndFfi sourceFunctions sourceHandler (fuel + 1)
      sourceState (some ([], ([], []), .skip, 0, 0)) (some functionLabel)
      arguments (some (handlerName, sourceHandlerBody, handlerLabel, entryLabel)) =
        some (.returned sourceHandlerState sourceValues) ∧
    evalWordCallWithHandlersAndFfi targetFunctions targetHandler (fuel + 1)
      targetState (some ([], ([], []), .skip, 0, 0)) (some functionLabel)
      colouredArguments
      (some (colour handlerName, targetHandlerBody, handlerLabel, entryLabel)) =
        some (.returned targetHandlerState targetValues) ∧
    WordColourStateRelation colour
      (writeRegister
        { sourceState with
          memory := sourceBodyState.memory
          privilege := sourceBodyState.privilege
          mode := sourceBodyState.mode }
        ⟨handlerName, hsourceHandlerName⟩
        (BitVec.ofNat width sourceException))
      (writeRegister
        { targetState with
          memory := targetBodyState.memory
          privilege := targetBodyState.privilege
          mode := targetBodyState.mode }
        ⟨colour handlerName, valid handlerName hsourceHandlerName⟩
        (BitVec.ofNat width targetException)) ∧
    WordColourStateRelation colour sourceHandlerState targetHandlerState ∧
    targetValues = sourceValues := by
  have hreturned : WordColourStateRelation colour
      { sourceState with
        memory := sourceBodyState.memory
        privilege := sourceBodyState.privilege
        mode := sourceBodyState.mode }
      { targetState with
        memory := targetBodyState.memory
        privilege := targetBodyState.privilege
        mode := targetBodyState.mode } := by
    constructor
    · exact hcallerRelation.pc
    · exact hbodyRelation.memory
    · exact hbodyRelation.privilege
    · exact hbodyRelation.mode
    · intro name hname hcolour
      exact hcallerRelation.register name hname hcolour
  have hentry := wordColourStateRelation_writeRegister colour valid injective
    colourZero
    { sourceState with
      memory := sourceBodyState.memory
      privilege := sourceBodyState.privilege
      mode := sourceBodyState.mode }
    { targetState with
      memory := targetBodyState.memory
      privilege := targetBodyState.privilege
      mode := targetBodyState.mode }
    hreturned handlerName hsourceHandlerName
    (BitVec.ofNat width sourceException) (BitVec.ofNat width targetException)
    (by simpa [hexception])
  have hsourceCall := evalWordCallWithHandlersAndFfi_raise_handler_of_eval
    sourceFunctions sourceHandler fuel sourceState sourceCallee sourceBodyState
    functionLabel parameters arguments sourceBody argumentValues sourceException
    handlerName handlerLabel entryLabel sourceHandlerBody
    ⟨handlerName, hsourceHandlerName⟩ (.returned sourceHandlerState sourceValues)
    hlookupSource hargumentsSource hbindSource hbodySource
    hsourceHandlerRegister hhandlerSource
  have htargetCall := evalWordCallWithHandlersAndFfi_raise_handler_of_eval
    targetFunctions targetHandler fuel targetState targetCallee targetBodyState
    functionLabel (parameters.map colour) colouredArguments targetBody
    argumentValues targetException (colour handlerName) handlerLabel entryLabel
    targetHandlerBody ⟨colour handlerName, valid handlerName hsourceHandlerName⟩
    (.returned targetHandlerState targetValues)
    hlookupTarget hargumentsTarget hbindTarget hbodyTarget
    htargetHandlerRegister hhandlerTarget
  exact ⟨hsourceCall, htargetCall, hentry, hhandlerRelation, hvalues⟩

end Flapjack.RiscV
