import Flapjack.Compiler.Backend.WordCse.ProductionAssign

namespace Flapjack.Test.WordCseProductionAssignParity
open Flapjack RiscV Compiler.Backend.WordCse

private def loadExpression : WordExp (BitVec 64) :=
  .load (.op .add [.var 9,.const 0])
private def seeded : WordCseKnowledge :=
  { toCanonical := (∅ : WordCseRegMap).insert 3 3 |>.insert 5 5 |>.insert 7 3 |>.insert 9 9
    toLatest := (∅ : WordCseRegMap).insert 3 5 |>.insert 9 9
    getsMem := (∅ : WordCseRegMap).insert (wordCseStoreCode (.currHeap : WordStore (BitVec 64))) 3
    instrsMem := (∅ : WordCseFactMap).insert [99] 3
    loadsMem := (∅ : WordCseFactMap).insert [21,109,0] 3 }

-- Original Assign is full identity, not the Mem load-fact update. Before the
-- repair empty input incorrectly acquired canonical7/load[21,109,0] facts.
example : (wordCseProg wordCseEmpty (.assign 7 loadExpression)).2.toCanonical[7]? = none := by decide +kernel
example : (wordCseProg wordCseEmpty (.assign 7 loadExpression)).2.loadsMem[[21,109,0]]? = none := by decide +kernel
example : (wordCseProg seeded (.assign 7 loadExpression)).2.toCanonical[7]? = some 3 := by decide +kernel
example : (wordCseProg seeded (.assign 7 loadExpression)).2.loadsMem[[21,109,0]]? = some 3 := by decide +kernel

private def knowledgeView (data : WordCseKnowledge) :=
  (data.toCanonical.toList,data.toLatest.toList,data.getsMem.toList,
   data.instrsMem.toList,data.loadsMem.toList)

def runChecks : IO Bool := do
  let expressions : List (WordExp (BitVec 64)) :=
    [loadExpression,.const 255,.var 9,.lookup .currHeap,
     .op .xor [.var 9,.const 3],.shift .lsl (.var 9) (.var 5),.load (.load (.var 9))]
  for data in [wordCseEmpty,seeded] do
    for destination in [2,7,9,1208925819614629174706183] do
      for value in expressions do
        let original := WordProg.assign destination value
        let output := wordCseProg data original
        if knowledgeView output.2 != knowledgeView data || reprStr output.1 != reprStr original then
          IO.eprintln s!"FAIL executed CSE Assign identity destination={destination}"
          return false
  IO.println "PASS executed CSE Assign: 56 full-state/program cases, all expression constructors, load alias/even/large destinations; four original-derived kernel observations and universal input-only transport"
  return true
end Flapjack.Test.WordCseProductionAssignParity
