import Flapjack.RiscV.WordCse
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.AllocatorMemoryInvariant

namespace Flapjack.WordAlloc
open RiscV

/-- Fact substitution emits either the supported input or a supported Move.
This is Flapjack runtime-domain infrastructure with no HOL original. -/
private theorem cseFactMemoryGuard {α : Type} (data : WordCseKnowledge)
    (table : WordCseFactMap) (register : Nat) (key : List Nat)
    (instruction : WordProg α) (insert : WordCseKnowledge → Nat → WordCseKnowledge)
    (supported : allocatorMemorySupported instruction = true) :
    allocatorMemorySupported (wordCseAddToFact data table register key instruction insert).1 = true := by
  unfold wordCseAddToFact
  split <;> split <;> simp_all [allocatorMemorySupported]

private theorem cseConstantMemoryGuard {α : Type} [WordCseHash α]
    (data : WordCseKnowledge) (register : Nat) (value : α) :
    allocatorMemorySupported (wordCseAddToDataConst data register value).1 = true := by
  unfold wordCseAddToDataConst
  dsimp only
  split <;> simp [allocatorMemorySupported]

/-- Complete actual instruction CSE preserves source memory support with
arbitrary knowledge, including offsets. Reusing a fact may remove an
unsupported operation, so unconditional equality is not asserted. No HOL
correctness statement is narrowed by this Flapjack-only guard theorem. -/
theorem cseInstructionMemoryGuard {α : Type} [WordCseHash α]
    (data : WordCseKnowledge) (instruction : WordInst α)
    (supported : allocatorMemorySupported (.inst instruction) = true) :
    allocatorMemorySupported (wordCseInst data instruction).1 = true := by
  cases instruction with
  | arith operation =>
      simp only [wordCseInst]
      split <;> simp_all [wordCseAddToData, cseFactMemoryGuard, allocatorMemorySupported]
  | const register value =>
      simp only [wordCseInst]
      split <;> simp_all [allocatorMemorySupported, cseConstantMemoryGuard]
  | mem operator register address =>
      simp only [wordCseInst]
      repeat' (split <;> simp_all [wordCseAddToLoad, cseFactMemoryGuard])
  | memOffset operator register address offset =>
      simp only [wordCseInst]
      repeat' (split <;> simp_all [wordCseAddToLoad, cseFactMemoryGuard])

/-- All actual CSE program cases retain supported memory operations, for
arbitrary knowledge and both Call continuations. This is production-domain
infrastructure, not a HOL pass-correctness port or target-run premise. -/
theorem cseProgramMemoryGuard {α : Type} [WordCseHash α]
    (data : WordCseKnowledge) (program : WordProg α)
    (supported : allocatorMemorySupported program = true) :
    allocatorMemorySupported (wordCseProg data program).1 = true := by
  fun_induction wordApplyColour (fun name => name) program generalizing data <;>
    simp_all [wordCseProg, allocatorMemorySupported, cseInstructionMemoryGuard, cseFactMemoryGuard]
  case case5 =>
    rename_i destination store
    cases (wordCseInvalidate data destination).getsMem[wordCseStoreCode store]? <;> simp_all
    all_goals split <;> simp_all [allocatorMemorySupported]
  case case7 =>
    cases ‹WordExp α› <;> simp_all
    all_goals repeat' (split <;> simp_all [allocatorMemorySupported])
  all_goals repeat' (split <;> simp_all [allocatorMemorySupported, cseFactMemoryGuard])

/-- The actual CSE wrapper retains input support without assumed output
support. Flapjack production infrastructure with no HOL original. -/
theorem cseWrapperMemoryGuard {α : Type} [WordCseHash α]
    (program : WordProg α) (supported : allocatorMemorySupported program = true) :
    allocatorMemorySupported (wordCseProp program) = true :=
  cseProgramMemoryGuard wordCseEmpty program supported

end Flapjack.WordAlloc
