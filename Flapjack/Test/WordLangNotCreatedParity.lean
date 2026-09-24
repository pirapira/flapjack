import Flapjack.Pancake.WordConvs
import Flapjack.Test.Runtime

/-!
# wordConvs `not_created_subprogs` / `no_*_subprogs` Lean regression

Kernel-checked cases matching the 15 rows of
`scripts/hol-probes/word_convs_not_created_probe.out`.
-/

namespace Flapjack.Test.WordLangNotCreatedParity

open Flapjack

private abbrev W := BitVec 8

private def cuts : WordLangCutsets :=
  ((FEMPTY : WordLangNumSet), (FEMPTY : WordLangNumSet))

private def skipP : WordLangProg W := .skip

private def allocEmpty : WordLangProg W := .alloc 0 cuts

private def allocOther : WordLangProg W := .alloc 1 cuts

private def seqAlloc : WordLangProg W := .seq .skip (.alloc 0 cuts)

private def mtSkip : WordLangProg W := .mustTerminate .skip

private def installEmpty : WordLangProg W := .install 0 0 0 0 cuts

private def shareArb : WordLangProg W := .shareInst wordLangArbMemOp 0 (.var 0)

private def shareLoad : WordLangProg W := .shareInst .load 0 (.var 0)

private def seqShare : WordLangProg W := .seq .skip shareArb

private def callNone : WordLangProg W := .call none none [] none

private def callHandlerMt : WordLangProg W :=
  .call none none [] (some (0, .mustTerminate .skip, 0, 0))

-- nac_skip=T
example : noAllocSubprogs skipP := by simp [noAllocSubprogs, notCreatedSubprogs, skipP]
-- nac_alloc_empty=F
example : ¬ noAllocSubprogs allocEmpty := by
  simp [noAllocSubprogs, notCreatedSubprogs, allocEmpty, cuts]
-- nac_alloc_other=F
example : ¬ noAllocSubprogs allocOther := by
  simp [noAllocSubprogs, notCreatedSubprogs, allocOther, cuts]
-- nac_seq_alloc=F
example : ¬ noAllocSubprogs seqAlloc := by
  simp [noAllocSubprogs, notCreatedSubprogs, seqAlloc, cuts]
-- nac_mt_skip=T
example : noAllocSubprogs mtSkip := by
  simp [noAllocSubprogs, notCreatedSubprogs, mtSkip]
-- nins_install_empty=F
example : ¬ noInstallSubprogs installEmpty := by
  simp [noInstallSubprogs, notCreatedSubprogs, installEmpty, cuts]
-- nmt_mt_skip=F
example : ¬ noMtSubprogs mtSkip := by
  simp [noMtSubprogs, notCreatedSubprogs, mtSkip]
-- nsi_skip=T
example : noShareInstSubprogs skipP := by
  simp [noShareInstSubprogs, notCreatedSubprogs, skipP]
-- nsi_share_arb=F
example : ¬ noShareInstSubprogs shareArb := by
  simp [noShareInstSubprogs, notCreatedSubprogs, shareArb]
-- nsi_share_load=F
example : ¬ noShareInstSubprogs shareLoad := by
  simp [noShareInstSubprogs, notCreatedSubprogs, shareLoad]
-- nsi_seq_share=F
example : ¬ noShareInstSubprogs seqShare := by
  simp [noShareInstSubprogs, notCreatedSubprogs, seqShare, shareArb]
-- nsi_call_none=T
example : noShareInstSubprogs callNone := by
  simp [noShareInstSubprogs, notCreatedSubprogs, callNone]
-- nsi_call_handler_mt=T
example : noShareInstSubprogs callHandlerMt := by
  simp [noShareInstSubprogs, notCreatedSubprogs, callHandlerMt]
-- nmt_call_handler_mt=F
example : ¬ noMtSubprogs callHandlerMt := by
  simp [noMtSubprogs, notCreatedSubprogs, callHandlerMt]
-- nac_install_empty=T
example : noAllocSubprogs installEmpty := by
  simp [noAllocSubprogs, notCreatedSubprogs, installEmpty, cuts]

def runChecks : IO Bool := do
  IO.println "PASS wordConvs not_created_subprogs no_alloc/no_install/no_mt/no_share_inst match all 15 oracle rows"
  pure true

end Flapjack.Test.WordLangNotCreatedParity