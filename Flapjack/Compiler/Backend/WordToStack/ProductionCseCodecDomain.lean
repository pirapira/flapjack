import Flapjack.RiscV.WordCse
import Flapjack.RiscV.Allocator
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

namespace Flapjack
open WordProgCarrierCodec
open RiscV

/-- Flapjack-only fact substitution preserves accepted program constructors. -/
private theorem factDomain {width : Nat} [WordCseHash (BitVec width)] (data : WordCseKnowledge)
    (table : WordCseFactMap) (register : Nat) (key : List Nat)
    (instruction : WordProg (BitVec width))
    (insert : WordCseKnowledge → Nat → WordCseKnowledge)
    (accepted : supportsCodec instruction = true) :
    supportsCodec (wordCseAddToFact data table register key instruction insert).1 = true := by
  unfold wordCseAddToFact
  split <;> split <;> simp_all [supportsCodec]

/-- Flapjack-only constant fact recording emits the original accepted constant. -/
private theorem constantDomain {width : Nat} [WordCseHash (BitVec width)] (data : WordCseKnowledge)
    (register : Nat) (value : BitVec width) :
    supportsCodec (wordCseAddToDataConst data register value).1 = true := by
  unfold wordCseAddToDataConst
  dsimp only
  split <;> simp [supportsCodec]

/-- Full actual instruction CSE codec domain, without well-formed knowledge
assumptions. The unsupported five-register primitive is never recorded. -/
private theorem cseInstructionDomain {width : Nat} [WordCseHash (BitVec width)] (data : WordCseKnowledge)
    (instruction : WordInst (BitVec width)) :
    supportsCodec (wordCseInst data instruction).1 = supportsCodec (.inst instruction) := by
  cases instruction with
  | arith operation =>
    cases operation <;> simp only [wordCseInst]
    all_goals try dsimp only
    -- Split the actual outer sharing decision before unfolding its dispatch.
    -- This works for arbitrary diagnostic instances; the five-register case
    -- still reduces to the literal false branch.
    all_goals first | rfl | skip
    all_goals split <;>
      simp_all [supportsCodec, wordCseAddToData, wordCseCanonicalArith, factDomain]
  | const register value =>
    simp [wordCseInst, supportsCodec]
    split <;> simp_all [supportsCodec, constantDomain]
  | mem operator register address =>
    simp only [wordCseInst]
    repeat' (split <;> simp_all [supportsCodec, wordCseAddToLoad, factDomain])
  | memOffset operator register address offset =>
    simp only [wordCseInst]
    repeat' (split <;> simp_all [supportsCodec, wordCseAddToLoad, factDomain])

/-- Full production CSE recursion, with arbitrary knowledge and both Call
continuations. Flapjack-only carrier closure, not a HOL theorem port. -/
private theorem cseDomain {width : Nat} [WordCseHash (BitVec width)] (data : WordCseKnowledge)
    (program : WordProg (BitVec width)) :
    supportsCodec (wordCseProg data program).1 = supportsCodec program := by
  fun_induction wordApplyColour (fun name => name) program generalizing data <;>
    simp_all [wordCseProg, supportsCodec, cseInstructionDomain,
      factDomain]
  case case5 =>
    rename_i destination store
    cases (wordCseInvalidate data destination).getsMem[wordCseStoreCode store]? <;>
      simp_all
    all_goals split <;> simp_all [supportsCodec]
  case case7 =>
    cases ‹WordExp (BitVec width)› <;> simp_all
    all_goals repeat' (split <;> simp_all [supportsCodec])
  all_goals repeat' (split <;> simp_all [supportsCodec, factDomain])

/-- Complete native codec-domain equality through the actual executed CSE
recursion for arbitrary knowledge. No desired output, valid-knowledge, codec
success or successful-pass premise is assumed. Flapjack-only infrastructure;
there is no HOL original theorem about the production partial codec. -/
theorem wordLangProgToHOL_wordCseProg_isSome {width : Nat} [WordCseHash (BitVec width)]
    (data : WordCseKnowledge) (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordCseProg data program).1).isSome =
      (wordLangProgToHOL program).isSome := by
  rw [codecDomain, codecDomain]
  exact cseDomain data program

/-- The actual production CSE wrapper preserves exactly the codec domain.
Other optimization passes and native frame/route remain separate obligations.
Flapjack-only carrier infrastructure, not a HOL port. -/
theorem wordLangProgToHOL_wordCseProp_isSome {width : Nat} [WordCseHash (BitVec width)]
    (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordCseProp program)).isSome =
      (wordLangProgToHOL program).isSome :=
  wordLangProgToHOL_wordCseProg_isSome wordCseEmpty program

end Flapjack
