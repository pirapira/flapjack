import Flapjack.Compiler.Backend.WordCse.ProductionFactAux

namespace Flapjack.Test.WordCseProductionFactAuxParity
open Flapjack RiscV Compiler.Backend.WordCse
private abbrev Observation := List (Option Nat) × List (Option Nat) × List (Option Nat) ×
    List (Option Nat) × List (Option Nat) × (Nat × Nat × List (Nat × Nat))
private def nativeData (mode : Nat) : Knowledge :=
  let table := Misc.BalancedMap.insert listCmp (if mode = 0 then [99] else [42])
    (if mode = 0 then 9 else 3) Misc.BalancedMap.empty
  { toCanonical := sptFromAList [(3,3),(9,9)]
    toLatest := sptFromAList (if mode = 2 then [(3,5),(9,9)] else [(9,9)])
    getsMem := [(.currHeap,9)]
    instrsMem := table, loadsMem := table }
private def regMap (xs : List (Nat × Nat)) : WordCseRegMap :=
  xs.foldr (fun entry m => m.insert entry.1 entry.2) ∅
private def executedData (mode : Nat) : WordCseKnowledge :=
  let table : WordCseFactMap := (∅ : WordCseFactMap).insert
    (if mode = 0 then [99] else [42]) (if mode = 0 then 9 else 3)
  { toCanonical := regMap [(3,3),(9,9)]
    toLatest := regMap (if mode = 2 then [(3,5),(9,9)] else [(9,9)])
    getsMem := regMap [(wordCseStoreCode (.currHeap : WordStore (BitVec 64)),9)]
    instrsMem := table, loadsMem := table }
private def nativeObservation (destination : Nat)
    (output : Knowledge × WordLangProgHOL (BitVec 64)) : Observation :=
  let data := output.1
  ([destination,3,9].map (fun k => sptLookup k data.toCanonical),
   [3,destination,9].map (fun k => sptLookup k data.toLatest),
   [WordStore.currHeap,WordStore.nextFree].map (fun s => data.getsMem.lookup s),
   [[42],[99]].map (fun k => Misc.BalancedMap.lookup listCmp k data.instrsMem),
   [[42],[99]].map (fun k => Misc.BalancedMap.lookup listCmp k data.loadsMem),
   match output.2 with
   | .move priority moves => (0,priority,moves)
   | .tick => (1,0,[])
   | _ => (2,0,[]))
private def executedObservation (destination : Nat)
    (output : WordProg (BitVec 64) × WordCseKnowledge) : Observation :=
  let data := output.2
  ([destination,3,9].map (fun k => data.toCanonical[k]?),
   [3,destination,9].map (fun k => data.toLatest[k]?),
   [WordStore.currHeap,WordStore.nextFree].map (fun s => data.getsMem[wordCseStoreCode (s : WordStore (BitVec 64))]?),
   [[42],[99]].map (fun k => data.instrsMem[k]?),
   [[42],[99]].map (fun k => data.loadsMem[k]?),
   match output.1 with
   | .move priority moves => (0,priority,moves)
   | .tick => (1,0,[])
   | _ => (2,0,[]))
private def nativeRun (load : Bool) (mode destination : Nat) :=
  if load then addToLoadAux (nativeData mode) destination [42] (.tick : WordLangProgHOL (BitVec 64))
  else addToDataAux (nativeData mode) destination [42] (.tick : WordLangProgHOL (BitVec 64))
private def executedRun (load : Bool) (mode destination : Nat) :=
  let data := executedData mode
  if load then wordCseAddToLoad data destination [42] (.tick : WordProg (BitVec 64))
  else wordCseAddToFact data data.instrsMem destination [42] (.tick : WordProg (BitVec 64))
    (fun data register => wordCseRecordInst data register [42])
-- Each expected tuple is a complete original HOL aux_data/aux_load EVAL row.
private def fixtures : List (Bool × Nat × Nat × Observation) := [
  (false,0,2,([none,some 3,some 9],[none,none,some 9],[some 9,none],[none,some 9],[none,some 9],(1,0,[]))),
  (false,0,7,([some 7,some 3,some 9],[none,some 7,some 9],[some 9,none],[some 7,some 9],[none,some 9],(1,0,[]))),
  (false,1,2,([none,some 3,some 9],[none,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(2,3)]))),
  (false,1,7,([some 3,some 3,some 9],[some 7,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(7,3)]))),
  (false,2,2,([none,some 3,some 9],[some 5,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(2,5)]))),
  (false,2,7,([some 3,some 3,some 9],[some 7,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(7,5)]))),
  (true,0,2,([none,some 3,some 9],[none,none,some 9],[some 9,none],[none,some 9],[none,some 9],(1,0,[]))),
  (true,0,7,([some 7,some 3,some 9],[none,some 7,some 9],[some 9,none],[none,some 9],[some 7,some 9],(1,0,[]))),
  (true,1,2,([none,some 3,some 9],[none,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(2,3)]))),
  (true,1,7,([some 3,some 3,some 9],[some 7,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(7,3)]))),
  (true,2,2,([none,some 3,some 9],[some 5,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(2,5)]))),
  (true,2,7,([some 3,some 3,some 9],[some 7,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(7,5)])))]

example : fixtures.all (fun (load,mode,destination,expected) =>
    nativeObservation destination (nativeRun load mode destination) == expected) = true := by decide +kernel

def runChecks : IO Bool := do
  for (load,mode,destination,expected) in fixtures do
    let observed := executedObservation destination (executedRun load mode destination)
    if observed != expected then
      IO.eprintln s!"FAIL executed CSE fact producer load={load} mode={mode} destination={destination}: {repr observed}"
      return false
  IO.println "PASS executed CSE complete instruction/load fact producers: 12 original/kernel/runtime cases, all five fields, hit/miss, even/odd destinations, current-holder/default and full returned Move/Tick"
  return true
end Flapjack.Test.WordCseProductionFactAuxParity
