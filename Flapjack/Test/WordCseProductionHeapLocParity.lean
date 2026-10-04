import Flapjack.Compiler.Backend.WordCse.ProductionHeapLoc

namespace Flapjack.Test.WordCseProductionHeapLocParity
open Flapjack RiscV Compiler.Backend.WordCse
private abbrev Observation := List (Option Nat) × List (Option Nat) × List (Option Nat) ×
    List (Option Nat) × List (Option Nat) × Nat × Nat × Nat × Nat
private structure Fixture where
  kind : Nat
  mode : Nat
  destination : Nat
  source : Nat
  location : Nat
  expected : Observation
private def operator : Nat → BinOp
  | 0 => .add | 1 => .sub | 2 => .and | 3 => .or | _ => .xor
private def canonicalEntries (mode : Nat) : List (Nat × Nat) :=
  [(3,3),(5,5),(9,if mode = 5 ∨ mode = 6 then 3 else 9)]
private def factKey (f : Fixture) : List Nat :=
  if f.mode = 1 ∨ f.mode = 5 ∨ (f.kind = 5 ∧ f.mode = 3) then
    if f.kind = 5 then [48,f.location]
    else opCurrHeapToNumList (operator f.kind) (if f.mode = 5 then 3 else 9)
  else [99]
private def nativeData (f : Fixture) : Knowledge :=
  { toCanonical := sptFromAList (canonicalEntries f.mode)
    toLatest := sptFromAList [(3,5),(9,9)]
    getsMem := [(.currHeap,3)]
    instrsMem := Misc.BalancedMap.insert listCmp (factKey f) 3 Misc.BalancedMap.empty
    loadsMem := Misc.BalancedMap.insert listCmp [99] 3 Misc.BalancedMap.empty }
private def regMap (xs : List (Nat × Nat)) : WordCseRegMap :=
  xs.foldr (fun e m => m.insert e.1 e.2) ∅
private def executedData (f : Fixture) : WordCseKnowledge :=
  { toCanonical := regMap (canonicalEntries f.mode)
    toLatest := regMap [(3,5),(9,9)]
    getsMem := regMap [(wordCseStoreCode (.currHeap : WordStore (BitVec 64)),3)]
    instrsMem := (∅ : WordCseFactMap).insert (factKey f) 3
    loadsMem := (∅ : WordCseFactMap).insert [99] 3 }
private def observedKey (f : Fixture) : List Nat :=
  if f.kind = 5 then [48,f.location] else
    opCurrHeapToNumList (operator f.kind)
      (canonicalRegs' f.destination (invalidateData (nativeData f) f.destination) f.source)
private def nativeProgram (f : Fixture) : WordLangProgHOL (BitVec 64) :=
  if f.kind = 5 then .locValue f.destination f.location
  else .opCurrHeap (operator f.kind) f.destination f.source
private def executedProgram (f : Fixture) : WordProg (BitVec 64) :=
  if f.kind = 5 then .locValue f.destination f.location
  else .opCurrHeap (operator f.kind) f.destination f.source
private def nativeObservation (f : Fixture)
    (output : Knowledge × WordLangProgHOL (BitVec 64)) : Observation :=
  let data := output.1
  ([f.destination,3,5,9].map (fun k => sptLookup k data.toCanonical),
   [3,f.destination,9].map (fun k => sptLookup k data.toLatest),
   [WordStore.currHeap,WordStore.nextFree].map (fun k => data.getsMem.lookup k),
   [observedKey f,factKey f,[99]].map (fun k => Misc.BalancedMap.lookup listCmp k data.instrsMem),
   [[99]].map (fun k => Misc.BalancedMap.lookup listCmp k data.loadsMem),
   match output.2 with
   | .opCurrHeap b r source => (1,arithOpToNum b,r,source)
   | .locValue r l => (2,48,r,l)
   | .move priority [(r,current)] => (0,priority,r,current)
   | _ => (3,0,0,0))
private def executedObservation (f : Fixture)
    (output : WordProg (BitVec 64) × WordCseKnowledge) : Observation :=
  let data := output.2
  ([f.destination,3,5,9].map (fun k => data.toCanonical[k]?),
   [3,f.destination,9].map (fun k => data.toLatest[k]?),
   [WordStore.currHeap,WordStore.nextFree].map
     (fun k => data.getsMem[wordCseStoreCode (k : WordStore (BitVec 64))]?),
   [observedKey f,factKey f,[99]].map (fun k => data.instrsMem[k]?),
   [[99]].map (fun k => data.loadsMem[k]?),
   match output.1 with
   | .opCurrHeap b r source => (1,arithOpToNum b,r,source)
   | .locValue r l => (2,48,r,l)
   | .move priority [(r,current)] => (0,priority,r,current)
   | _ => (3,0,0,0))
-- Full numeric tuples strictly transcribed from original heap_loc_0..heap_loc_51.
private def fixtures : List Fixture := [
  ⟨0,0,7,9,0,([some 7, some 3, some 5, some 9],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],1,35,7,9)⟩,
  ⟨0,1,7,9,0,([some 3, some 3, some 5, some 9],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨0,2,2,9,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],1,35,2,9)⟩,
  ⟨0,3,7,8,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],1,35,7,8)⟩,
  ⟨0,4,9,9,0,([none, none, none, none],[none, none, none],[none, none],[none, none, none],[none],1,35,9,9)⟩,
  ⟨0,5,7,9,0,([some 3, some 3, some 5, some 3],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨0,6,7,9,0,([some 7, some 3, some 5, some 3],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],1,35,7,9)⟩,
  ⟨0,7,1208925819614629174706183,9,0,([some 1208925819614629174706183, some 3, some 5, some 9],[some 5, some 1208925819614629174706183, some 9],[some 3, none],[some 1208925819614629174706183, some 3, some 3],[some 3],1,35,1208925819614629174706183,9)⟩,
  ⟨1,0,7,9,0,([some 7, some 3, some 5, some 9],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],1,36,7,9)⟩,
  ⟨1,1,7,9,0,([some 3, some 3, some 5, some 9],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨1,2,2,9,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],1,36,2,9)⟩,
  ⟨1,3,7,8,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],1,36,7,8)⟩,
  ⟨1,4,9,9,0,([none, none, none, none],[none, none, none],[none, none],[none, none, none],[none],1,36,9,9)⟩,
  ⟨1,5,7,9,0,([some 3, some 3, some 5, some 3],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨1,6,7,9,0,([some 7, some 3, some 5, some 3],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],1,36,7,9)⟩,
  ⟨1,7,1208925819614629174706183,9,0,([some 1208925819614629174706183, some 3, some 5, some 9],[some 5, some 1208925819614629174706183, some 9],[some 3, none],[some 1208925819614629174706183, some 3, some 3],[some 3],1,36,1208925819614629174706183,9)⟩,
  ⟨2,0,7,9,0,([some 7, some 3, some 5, some 9],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],1,37,7,9)⟩,
  ⟨2,1,7,9,0,([some 3, some 3, some 5, some 9],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨2,2,2,9,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],1,37,2,9)⟩,
  ⟨2,3,7,8,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],1,37,7,8)⟩,
  ⟨2,4,9,9,0,([none, none, none, none],[none, none, none],[none, none],[none, none, none],[none],1,37,9,9)⟩,
  ⟨2,5,7,9,0,([some 3, some 3, some 5, some 3],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨2,6,7,9,0,([some 7, some 3, some 5, some 3],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],1,37,7,9)⟩,
  ⟨2,7,1208925819614629174706183,9,0,([some 1208925819614629174706183, some 3, some 5, some 9],[some 5, some 1208925819614629174706183, some 9],[some 3, none],[some 1208925819614629174706183, some 3, some 3],[some 3],1,37,1208925819614629174706183,9)⟩,
  ⟨3,0,7,9,0,([some 7, some 3, some 5, some 9],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],1,38,7,9)⟩,
  ⟨3,1,7,9,0,([some 3, some 3, some 5, some 9],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨3,2,2,9,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],1,38,2,9)⟩,
  ⟨3,3,7,8,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],1,38,7,8)⟩,
  ⟨3,4,9,9,0,([none, none, none, none],[none, none, none],[none, none],[none, none, none],[none],1,38,9,9)⟩,
  ⟨3,5,7,9,0,([some 3, some 3, some 5, some 3],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨3,6,7,9,0,([some 7, some 3, some 5, some 3],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],1,38,7,9)⟩,
  ⟨3,7,1208925819614629174706183,9,0,([some 1208925819614629174706183, some 3, some 5, some 9],[some 5, some 1208925819614629174706183, some 9],[some 3, none],[some 1208925819614629174706183, some 3, some 3],[some 3],1,38,1208925819614629174706183,9)⟩,
  ⟨4,0,7,9,0,([some 7, some 3, some 5, some 9],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],1,39,7,9)⟩,
  ⟨4,1,7,9,0,([some 3, some 3, some 5, some 9],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨4,2,2,9,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],1,39,2,9)⟩,
  ⟨4,3,7,8,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],1,39,7,8)⟩,
  ⟨4,4,9,9,0,([none, none, none, none],[none, none, none],[none, none],[none, none, none],[none],1,39,9,9)⟩,
  ⟨4,5,7,9,0,([some 3, some 3, some 5, some 3],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨4,6,7,9,0,([some 7, some 3, some 5, some 3],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],1,39,7,9)⟩,
  ⟨4,7,1208925819614629174706183,9,0,([some 1208925819614629174706183, some 3, some 5, some 9],[some 5, some 1208925819614629174706183, some 9],[some 3, none],[some 1208925819614629174706183, some 3, some 3],[some 3],1,39,1208925819614629174706183,9)⟩,
  ⟨5,0,7,9,0,([some 7, some 3, some 5, some 9],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],2,48,7,0)⟩,
  ⟨5,0,7,9,23,([some 7, some 3, some 5, some 9],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],2,48,7,23)⟩,
  ⟨5,0,7,9,1208925819614629174706193,([some 7, some 3, some 5, some 9],[some 5, some 7, some 9],[some 3, none],[some 7, some 3, some 3],[some 3],2,48,7,1208925819614629174706193)⟩,
  ⟨5,1,7,9,0,([some 3, some 3, some 5, some 9],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨5,1,7,9,23,([some 3, some 3, some 5, some 9],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨5,1,7,9,1208925819614629174706193,([some 3, some 3, some 5, some 9],[some 7, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,7,5)⟩,
  ⟨5,2,2,9,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],2,48,2,0)⟩,
  ⟨5,2,2,9,23,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],2,48,2,23)⟩,
  ⟨5,2,2,9,1208925819614629174706193,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[none, some 3, some 3],[some 3],2,48,2,1208925819614629174706193)⟩,
  ⟨5,3,2,8,0,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,2,5)⟩,
  ⟨5,3,2,8,23,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,2,5)⟩,
  ⟨5,3,2,8,1208925819614629174706193,([none, some 3, some 5, some 9],[some 5, none, some 9],[some 3, none],[some 3, some 3, none],[some 3],0,0,2,5)⟩ ]
example : fixtures.all (fun f => nativeObservation f (wordCse (nativeData f) (nativeProgram f)) == f.expected) = true := by decide +kernel
def runChecks : IO Bool := do
  for fixture in fixtures do
    let observed := executedObservation fixture
      (RiscV.wordCseProg (executedData fixture) (executedProgram fixture))
    if observed != fixture.expected then
      IO.eprintln s!"FAIL executed CSE heap/location kind={fixture.kind} mode={fixture.mode}: {repr observed}"
      return false
  IO.println "PASS executed CSE heap/location: 52 original/kernel/runtime cases, all five operators, full knowledge/program outputs, guards, canonical hit/miss, even destinations and large Nat registers/locations"
  return true
end Flapjack.Test.WordCseProductionHeapLocParity
