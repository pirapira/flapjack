import Flapjack.Compiler.Backend.WordCse.ProductionJoin

namespace Flapjack.Test.WordCseProductionJoinParity
open Flapjack RiscV Compiler.Backend.WordCse

private def facts (xs : List (List Nat × Nat)) : Misc.BalancedMap.Map (List Nat) Nat :=
  xs.foldr (fun entry m => Misc.BalancedMap.insert listCmp entry.1 entry.2 m) .tip
private def regMap (xs : List (Nat × Nat)) : WordCseRegMap :=
  xs.foldr (fun entry m => m.insert entry.1 entry.2) ∅
private def factMap (xs : List (List Nat × Nat)) : WordCseFactMap :=
  xs.foldr (fun entry m => m.insert entry.1 entry.2) ∅
private def stores : List WordStoreHOL := [.currHeap,.nextFree,.endOfHeap,.temp 3]
private def code (s : WordStoreHOL) : Nat :=
  wordCseStoreCode (wordStoreFromHOL s : WordStore (BitVec 64))
private def nativeFirst : Knowledge :=
  { toCanonical := sptFromAList [(1,11),(3,33),(5,55)]
    toLatest := sptFromAList [(1,99)]
    getsMem := [(.currHeap,11),(.nextFree,33),(.endOfHeap,55)]
    instrsMem := facts [([],11),([1],33),([1,2],55)]
    loadsMem := facts [([],11),([1],33),([1,2],55)] }
private def nativeSecond : Knowledge :=
  { toCanonical := sptFromAList [(1,11),(3,333),(7,77)]
    toLatest := sptFromAList [(1,99)]
    getsMem := [(.currHeap,11),(.nextFree,333),(.temp 3,77)]
    instrsMem := facts [([],11),([1],333),([7],77)]
    loadsMem := facts [([],11),([1],333),([7],77)] }
private def executedFirst : WordCseKnowledge :=
  { toCanonical := regMap [(1,11),(3,33),(5,55)]
    toLatest := regMap [(1,99)]
    getsMem := regMap [(code .currHeap,11),(code .nextFree,33),(code .endOfHeap,55)]
    instrsMem := factMap [([],11),([1],33),([1,2],55)]
    loadsMem := factMap [([],11),([1],33),([1,2],55)] }
private def executedSecond : WordCseKnowledge :=
  { toCanonical := regMap [(1,11),(3,333),(7,77)]
    toLatest := regMap [(1,99)]
    getsMem := regMap [(code .currHeap,11),(code .nextFree,333),(code (.temp 3),77)]
    instrsMem := factMap [([],11),([1],333),([7],77)]
    loadsMem := factMap [([],11),([1],333),([7],77)] }
private def nativeObservation (data : Knowledge) :=
  ([1,3,5,7].map (fun k => sptLookup k data.toCanonical),
   [1,3].map (fun k => sptLookup k data.toLatest),
   stores.map (fun s => data.getsMem.lookup s),
   [[],[1],[1,2],[7]].map (fun k => Misc.BalancedMap.lookup listCmp k data.instrsMem),
   [[],[1],[1,2],[7]].map (fun k => Misc.BalancedMap.lookup listCmp k data.loadsMem))
private def executedObservation (data : WordCseKnowledge) :=
  ([1,3,5,7].map (fun k => data.toCanonical[k]?),
   [1,3].map (fun k => data.toLatest[k]?),
   stores.map (fun s => data.getsMem[code s]?),
   [[],[1],[1,2],[7]].map (fun k => data.instrsMem[k]?),
   [[],[1],[1,2],[7]].map (fun k => data.loadsMem[k]?))
-- Complete five-field original join_fields EVAL observation.
private def expected : List (Option Nat) × List (Option Nat) × List (Option Nat) ×
    List (Option Nat) × List (Option Nat) :=
  ([some 11,none,none,none], [none,none], [some 11,none,none,none],
   [some 11,none,none,none], [some 11,none,none,none])
example : nativeObservation (mergeData nativeFirst nativeSecond) = expected := by decide +kernel
example : mergeData emptyData emptyData = emptyData := by decide
-- Duplicate native store keys are outside wfData: filtering can reveal a
-- later value hidden from first-match lookup. The map join must drop the key.
private def duplicateFirst : Knowledge :=
  { emptyData with getsMem := [(.currHeap,11),(.currHeap,33)] }
private def duplicateSecond : Knowledge :=
  { emptyData with getsMem := [(.currHeap,33)] }
example : duplicateFirst.getsMem.lookup .currHeap = some 11 ∧
    (mergeData duplicateFirst duplicateSecond).getsMem.lookup .currHeap = some 33 ∧
    ¬ (duplicateFirst.getsMem.map Prod.fst).Nodup := by decide

def runChecks : IO Bool := do
  let observed := executedObservation (wordCseMergeData executedFirst executedSecond)
  if observed != expected then
    IO.eprintln s!"FAIL executed CSE join: {repr observed}"
    return false
  let duplicate := wordCseMergeData
    { wordCseEmpty with getsMem := regMap [(code .currHeap,11)] }
    { wordCseEmpty with getsMem := regMap [(code .currHeap,33)] }
  if duplicate.getsMem[code .currHeap]? != none then
    IO.eprintln "FAIL executed CSE duplicate-key boundary"
    return false
  let empty := executedObservation (wordCseMergeData wordCseEmpty wordCseEmpty)
  if empty != executedObservation wordCseEmpty then
    IO.eprintln "FAIL executed CSE empty join"
    return false
  IO.println "PASS executed CSE join: all five fields, equal/conflicting/missing keys, latest reset, empty join and duplicate-key boundary; original HOL captures and kernel fixtures"
  return true

end Flapjack.Test.WordCseProductionJoinParity
