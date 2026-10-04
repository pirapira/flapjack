import Flapjack.Compiler.Backend.WordCse.ProductionMemory

namespace Flapjack.Test.WordCseProductionMemoryParity
open Flapjack RiscV Compiler.Backend.WordCse Compiler.Encoders.Asm

private abbrev Observation := List (Option Nat) × List (Option Nat) × List (Option Nat) ×
    List (Option Nat) × List (Option Nat) × Nat × Nat × Nat × Nat × Nat
private structure Fixture where
  width : Nat
  operator : WordMemOp
  mode : Nat
  offset : Nat
  destination : Nat
  address : Nat
  expected : Observation
private def regMap (xs : List (Nat × Nat)) : WordCseRegMap :=
  xs.foldr (fun entry m => m.insert entry.1 entry.2) ∅
private def canonicalEntries (mode : Nat) : List (Nat × Nat) :=
  [(3,3),(5,5),(9,if mode = 5 ∨ mode = 6 then 3 else 9)]
private def factKey {width : Nat} [NeZero width] (mode : Nat)
    (operator : WordMemOp) (offset : BitVec width) : List Nat :=
  if mode = 0 ∨ mode = 6 then [99]
  else loadToNumList operator (if mode = 5 then 3 else 9) offset
private def nativeData {width : Nat} [NeZero width] (mode : Nat)
    (operator : WordMemOp) (offset : BitVec width) : Knowledge :=
  { toCanonical := sptFromAList (canonicalEntries mode)
    toLatest := sptFromAList [(3,5),(9,9)]
    getsMem := [(.currHeap,3)]
    instrsMem := Misc.BalancedMap.insert listCmp [99] 3 Misc.BalancedMap.empty
    loadsMem := Misc.BalancedMap.insert listCmp (factKey mode operator offset) 3 Misc.BalancedMap.empty }
private def executedData {width : Nat} [NeZero width] (mode : Nat)
    (operator : WordMemOp) (offset : BitVec width) : WordCseKnowledge :=
  { toCanonical := regMap (canonicalEntries mode)
    toLatest := regMap [(3,5),(9,9)]
    getsMem := regMap [(wordCseStoreCode (.currHeap : WordStore (BitVec width)),3)]
    instrsMem := (∅ : WordCseFactMap).insert [99] 3
    loadsMem := (∅ : WordCseFactMap).insert (factKey mode operator offset) 3 }
private def nativeObservation {width : Nat} [NeZero width] (operator : WordMemOp)
    (destination : Nat) (offset : BitVec width)
    (output : Knowledge × WordLangProgHOL (BitVec width)) : Observation :=
  let data := output.1
  ([destination,3,5,9].map (fun k => sptLookup k data.toCanonical),
   [3,destination,9].map (fun k => sptLookup k data.toLatest),
   [WordStore.currHeap,WordStore.nextFree].map (fun s => data.getsMem.lookup s),
   [[99]].map (fun k => Misc.BalancedMap.lookup listCmp k data.instrsMem),
   [loadToNumList operator 9 offset,loadToNumList operator 3 offset,[99]].map
     (fun k => Misc.BalancedMap.lookup listCmp k data.loadsMem),
   match output.2 with
   | .inst (.mem op r (.addr a ofs)) => (1,memOpToNum op,r,a,ofs.toNat)
   | .move priority [(r,current)] => (0,priority,r,current,0)
   | _ => (2,0,0,0,0))
private def executedObservation {width : Nat} [NeZero width] (operator : WordMemOp)
    (destination : Nat) (offset : BitVec width)
    (output : WordProg (BitVec width) × WordCseKnowledge) : Observation :=
  let data := output.2
  ([destination,3,5,9].map (fun k => data.toCanonical[k]?),
   [3,destination,9].map (fun k => data.toLatest[k]?),
   [WordStore.currHeap,WordStore.nextFree].map
     (fun s => data.getsMem[wordCseStoreCode (s : WordStore (BitVec width))]?),
   [[99]].map (fun k => data.instrsMem[k]?),
   [loadToNumList operator 9 offset,loadToNumList operator 3 offset,[99]].map
     (fun k => data.loadsMem[k]?),
   match output.1 with
   | .inst (.mem op r a) => (1,wordCseMemOpToNum op,r,a,0)
   | .inst (.memOffset op r a ofs) => (1,wordCseMemOpToNum op,r,a,ofs.toNat)
   | .move priority [(r,current)] => (0,priority,r,current,0)
   | _ => (2,0,0,0,0))
-- Complete numeric tuples transcribed from original memory_0..memory_255.
private def fixtures : List Fixture := [
  ⟨64,.load,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,21,7,9,0)⟩,
  ⟨64,.load,0,18446744073709551615,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,21,7,9,18446744073709551615)⟩,
  ⟨64,.load,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨64,.load,1,18446744073709551615,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨64,.load,2,0,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,21,2,9,0)⟩,
  ⟨64,.load,2,18446744073709551615,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,21,2,9,18446744073709551615)⟩,
  ⟨64,.load,3,0,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,21,7,8,0)⟩,
  ⟨64,.load,3,18446744073709551615,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,21,7,8,18446744073709551615)⟩,
  ⟨64,.load,4,0,9,9,([none,none,none,none],[none,none,none],[none,none],[none],[none,none,none],1,21,9,9,0)⟩,
  ⟨64,.load,4,18446744073709551615,9,9,([none,none,none,none],[none,none,none],[none,none],[none],[none,none,none],1,21,9,9,18446744073709551615)⟩,
  ⟨64,.load,5,0,7,9,([some 3,some 3,some 5,some 3],[some 7,none,some 9],[some 3,none],[some 3],[none,some 3,none],0,0,7,5,0)⟩,
  ⟨64,.load,5,18446744073709551615,7,9,([some 3,some 3,some 5,some 3],[some 7,none,some 9],[some 3,none],[some 3],[none,some 3,none],0,0,7,5,0)⟩,
  ⟨64,.load,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,21,7,9,0)⟩,
  ⟨64,.load,6,18446744073709551615,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,21,7,9,18446744073709551615)⟩,
  ⟨64,.load8,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,22,7,9,0)⟩,
  ⟨64,.load8,0,18446744073709551615,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,22,7,9,18446744073709551615)⟩,
  ⟨64,.load8,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨64,.load8,1,18446744073709551615,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨64,.load8,2,0,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,22,2,9,0)⟩,
  ⟨64,.load8,2,18446744073709551615,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,22,2,9,18446744073709551615)⟩,
  ⟨64,.load8,3,0,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,22,7,8,0)⟩,
  ⟨64,.load8,3,18446744073709551615,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,22,7,8,18446744073709551615)⟩,
  ⟨64,.load8,4,0,9,9,([none,none,none,none],[none,none,none],[none,none],[none],[none,none,none],1,22,9,9,0)⟩,
  ⟨64,.load8,4,18446744073709551615,9,9,([none,none,none,none],[none,none,none],[none,none],[none],[none,none,none],1,22,9,9,18446744073709551615)⟩,
  ⟨64,.load8,5,0,7,9,([some 3,some 3,some 5,some 3],[some 7,none,some 9],[some 3,none],[some 3],[none,some 3,none],0,0,7,5,0)⟩,
  ⟨64,.load8,5,18446744073709551615,7,9,([some 3,some 3,some 5,some 3],[some 7,none,some 9],[some 3,none],[some 3],[none,some 3,none],0,0,7,5,0)⟩,
  ⟨64,.load8,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,22,7,9,0)⟩,
  ⟨64,.load8,6,18446744073709551615,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,22,7,9,18446744073709551615)⟩,
  ⟨64,.load16,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,46,7,9,0)⟩,
  ⟨64,.load16,0,18446744073709551615,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,46,7,9,18446744073709551615)⟩,
  ⟨64,.load16,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨64,.load16,1,18446744073709551615,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨64,.load16,2,0,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,46,2,9,0)⟩,
  ⟨64,.load16,2,18446744073709551615,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,46,2,9,18446744073709551615)⟩,
  ⟨64,.load16,3,0,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,46,7,8,0)⟩,
  ⟨64,.load16,3,18446744073709551615,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,46,7,8,18446744073709551615)⟩,
  ⟨64,.load16,4,0,9,9,([none,none,none,none],[none,none,none],[none,none],[none],[none,none,none],1,46,9,9,0)⟩,
  ⟨64,.load16,4,18446744073709551615,9,9,([none,none,none,none],[none,none,none],[none,none],[none],[none,none,none],1,46,9,9,18446744073709551615)⟩,
  ⟨64,.load16,5,0,7,9,([some 3,some 3,some 5,some 3],[some 7,none,some 9],[some 3,none],[some 3],[none,some 3,none],0,0,7,5,0)⟩,
  ⟨64,.load16,5,18446744073709551615,7,9,([some 3,some 3,some 5,some 3],[some 7,none,some 9],[some 3,none],[some 3],[none,some 3,none],0,0,7,5,0)⟩,
  ⟨64,.load16,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,46,7,9,0)⟩,
  ⟨64,.load16,6,18446744073709551615,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,46,7,9,18446744073709551615)⟩,
  ⟨64,.load32,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,44,7,9,0)⟩,
  ⟨64,.load32,0,18446744073709551615,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,44,7,9,18446744073709551615)⟩,
  ⟨64,.load32,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨64,.load32,1,18446744073709551615,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨64,.load32,2,0,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,44,2,9,0)⟩,
  ⟨64,.load32,2,18446744073709551615,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,44,2,9,18446744073709551615)⟩,
  ⟨64,.load32,3,0,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,44,7,8,0)⟩,
  ⟨64,.load32,3,18446744073709551615,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[some 3,none,none],1,44,7,8,18446744073709551615)⟩,
  ⟨64,.load32,4,0,9,9,([none,none,none,none],[none,none,none],[none,none],[none],[none,none,none],1,44,9,9,0)⟩,
  ⟨64,.load32,4,18446744073709551615,9,9,([none,none,none,none],[none,none,none],[none,none],[none],[none,none,none],1,44,9,9,18446744073709551615)⟩,
  ⟨64,.load32,5,0,7,9,([some 3,some 3,some 5,some 3],[some 7,none,some 9],[some 3,none],[some 3],[none,some 3,none],0,0,7,5,0)⟩,
  ⟨64,.load32,5,18446744073709551615,7,9,([some 3,some 3,some 5,some 3],[some 7,none,some 9],[some 3,none],[some 3],[none,some 3,none],0,0,7,5,0)⟩,
  ⟨64,.load32,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,44,7,9,0)⟩,
  ⟨64,.load32,6,18446744073709551615,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,44,7,9,18446744073709551615)⟩,
  ⟨64,.store,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨64,.store,0,18446744073709551615,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,18446744073709551615)⟩,
  ⟨64,.store,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨64,.store,1,18446744073709551615,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,18446744073709551615)⟩,
  ⟨64,.store,2,0,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,2,9,0)⟩,
  ⟨64,.store,2,18446744073709551615,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,2,9,18446744073709551615)⟩,
  ⟨64,.store,3,0,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,8,0)⟩,
  ⟨64,.store,3,18446744073709551615,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,8,18446744073709551615)⟩,
  ⟨64,.store,4,0,9,9,([some 9,some 3,some 5,some 9],[some 5,some 9,some 9],[some 3,none],[some 3],[none,none,none],1,23,9,9,0)⟩,
  ⟨64,.store,4,18446744073709551615,9,9,([some 9,some 3,some 5,some 9],[some 5,some 9,some 9],[some 3,none],[some 3],[none,none,none],1,23,9,9,18446744073709551615)⟩,
  ⟨64,.store,5,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨64,.store,5,18446744073709551615,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,18446744073709551615)⟩,
  ⟨64,.store,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨64,.store,6,18446744073709551615,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,18446744073709551615)⟩,
  ⟨64,.store8,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨64,.store8,0,18446744073709551615,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,18446744073709551615)⟩,
  ⟨64,.store8,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨64,.store8,1,18446744073709551615,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,18446744073709551615)⟩,
  ⟨64,.store8,2,0,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,2,9,0)⟩,
  ⟨64,.store8,2,18446744073709551615,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,2,9,18446744073709551615)⟩,
  ⟨64,.store8,3,0,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,8,0)⟩,
  ⟨64,.store8,3,18446744073709551615,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,8,18446744073709551615)⟩,
  ⟨64,.store8,4,0,9,9,([some 9,some 3,some 5,some 9],[some 5,some 9,some 9],[some 3,none],[some 3],[none,none,none],1,47,9,9,0)⟩,
  ⟨64,.store8,4,18446744073709551615,9,9,([some 9,some 3,some 5,some 9],[some 5,some 9,some 9],[some 3,none],[some 3],[none,none,none],1,47,9,9,18446744073709551615)⟩,
  ⟨64,.store8,5,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨64,.store8,5,18446744073709551615,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,18446744073709551615)⟩,
  ⟨64,.store8,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨64,.store8,6,18446744073709551615,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,18446744073709551615)⟩,
  ⟨64,.store16,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨64,.store16,0,18446744073709551615,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,18446744073709551615)⟩,
  ⟨64,.store16,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨64,.store16,1,18446744073709551615,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,18446744073709551615)⟩,
  ⟨64,.store16,2,0,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,2,9,0)⟩,
  ⟨64,.store16,2,18446744073709551615,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,2,9,18446744073709551615)⟩,
  ⟨64,.store16,3,0,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,8,0)⟩,
  ⟨64,.store16,3,18446744073709551615,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,8,18446744073709551615)⟩,
  ⟨64,.store16,4,0,9,9,([some 9,some 3,some 5,some 9],[some 5,some 9,some 9],[some 3,none],[some 3],[none,none,none],1,24,9,9,0)⟩,
  ⟨64,.store16,4,18446744073709551615,9,9,([some 9,some 3,some 5,some 9],[some 5,some 9,some 9],[some 3,none],[some 3],[none,none,none],1,24,9,9,18446744073709551615)⟩,
  ⟨64,.store16,5,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨64,.store16,5,18446744073709551615,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,18446744073709551615)⟩,
  ⟨64,.store16,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨64,.store16,6,18446744073709551615,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,18446744073709551615)⟩,
  ⟨64,.store32,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨64,.store32,0,18446744073709551615,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,18446744073709551615)⟩,
  ⟨64,.store32,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨64,.store32,1,18446744073709551615,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,18446744073709551615)⟩,
  ⟨64,.store32,2,0,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,2,9,0)⟩,
  ⟨64,.store32,2,18446744073709551615,2,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,2,9,18446744073709551615)⟩,
  ⟨64,.store32,3,0,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,8,0)⟩,
  ⟨64,.store32,3,18446744073709551615,7,8,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,8,18446744073709551615)⟩,
  ⟨64,.store32,4,0,9,9,([some 9,some 3,some 5,some 9],[some 5,some 9,some 9],[some 3,none],[some 3],[none,none,none],1,45,9,9,0)⟩,
  ⟨64,.store32,4,18446744073709551615,9,9,([some 9,some 3,some 5,some 9],[some 5,some 9,some 9],[some 3,none],[some 3],[none,none,none],1,45,9,9,18446744073709551615)⟩,
  ⟨64,.store32,5,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨64,.store32,5,18446744073709551615,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,18446744073709551615)⟩,
  ⟨64,.store32,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨64,.store32,6,18446744073709551615,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,18446744073709551615)⟩,
  ⟨1,.load,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,21,7,9,0)⟩,
  ⟨1,.load,0,1,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,21,7,9,1)⟩,
  ⟨1,.load,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨1,.load,1,1,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨1,.load,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,21,7,9,0)⟩,
  ⟨1,.load,6,1,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,21,7,9,1)⟩,
  ⟨1,.load8,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,22,7,9,0)⟩,
  ⟨1,.load8,0,1,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,22,7,9,1)⟩,
  ⟨1,.load8,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨1,.load8,1,1,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨1,.load8,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,22,7,9,0)⟩,
  ⟨1,.load8,6,1,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,22,7,9,1)⟩,
  ⟨1,.load16,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,46,7,9,0)⟩,
  ⟨1,.load16,0,1,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,46,7,9,1)⟩,
  ⟨1,.load16,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨1,.load16,1,1,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨1,.load16,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,46,7,9,0)⟩,
  ⟨1,.load16,6,1,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,46,7,9,1)⟩,
  ⟨1,.load32,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,44,7,9,0)⟩,
  ⟨1,.load32,0,1,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,44,7,9,1)⟩,
  ⟨1,.load32,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨1,.load32,1,1,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨1,.load32,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,44,7,9,0)⟩,
  ⟨1,.load32,6,1,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,44,7,9,1)⟩,
  ⟨1,.store,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨1,.store,0,1,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,1)⟩,
  ⟨1,.store,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨1,.store,1,1,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,1)⟩,
  ⟨1,.store,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨1,.store,6,1,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,1)⟩,
  ⟨1,.store8,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨1,.store8,0,1,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,1)⟩,
  ⟨1,.store8,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨1,.store8,1,1,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,1)⟩,
  ⟨1,.store8,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨1,.store8,6,1,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,1)⟩,
  ⟨1,.store16,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨1,.store16,0,1,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,1)⟩,
  ⟨1,.store16,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨1,.store16,1,1,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,1)⟩,
  ⟨1,.store16,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨1,.store16,6,1,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,1)⟩,
  ⟨1,.store32,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨1,.store32,0,1,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,1)⟩,
  ⟨1,.store32,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨1,.store32,1,1,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,1)⟩,
  ⟨1,.store32,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨1,.store32,6,1,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,1)⟩,
  ⟨8,.load,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,21,7,9,0)⟩,
  ⟨8,.load,0,255,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,21,7,9,255)⟩,
  ⟨8,.load,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨8,.load,1,255,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨8,.load,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,21,7,9,0)⟩,
  ⟨8,.load,6,255,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,21,7,9,255)⟩,
  ⟨8,.load8,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,22,7,9,0)⟩,
  ⟨8,.load8,0,255,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,22,7,9,255)⟩,
  ⟨8,.load8,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨8,.load8,1,255,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨8,.load8,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,22,7,9,0)⟩,
  ⟨8,.load8,6,255,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,22,7,9,255)⟩,
  ⟨8,.load16,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,46,7,9,0)⟩,
  ⟨8,.load16,0,255,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,46,7,9,255)⟩,
  ⟨8,.load16,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨8,.load16,1,255,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨8,.load16,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,46,7,9,0)⟩,
  ⟨8,.load16,6,255,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,46,7,9,255)⟩,
  ⟨8,.load32,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,44,7,9,0)⟩,
  ⟨8,.load32,0,255,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,44,7,9,255)⟩,
  ⟨8,.load32,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨8,.load32,1,255,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨8,.load32,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,44,7,9,0)⟩,
  ⟨8,.load32,6,255,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,44,7,9,255)⟩,
  ⟨8,.store,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨8,.store,0,255,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,255)⟩,
  ⟨8,.store,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨8,.store,1,255,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,255)⟩,
  ⟨8,.store,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨8,.store,6,255,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,255)⟩,
  ⟨8,.store8,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨8,.store8,0,255,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,255)⟩,
  ⟨8,.store8,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨8,.store8,1,255,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,255)⟩,
  ⟨8,.store8,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨8,.store8,6,255,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,255)⟩,
  ⟨8,.store16,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨8,.store16,0,255,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,255)⟩,
  ⟨8,.store16,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨8,.store16,1,255,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,255)⟩,
  ⟨8,.store16,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨8,.store16,6,255,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,255)⟩,
  ⟨8,.store32,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨8,.store32,0,255,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,255)⟩,
  ⟨8,.store32,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨8,.store32,1,255,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,255)⟩,
  ⟨8,.store32,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨8,.store32,6,255,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,255)⟩,
  ⟨80,.load,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,21,7,9,0)⟩,
  ⟨80,.load,0,1208925819614629174706175,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,21,7,9,1208925819614629174706175)⟩,
  ⟨80,.load,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨80,.load,1,1208925819614629174706175,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨80,.load,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,21,7,9,0)⟩,
  ⟨80,.load,6,1208925819614629174706175,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,21,7,9,1208925819614629174706175)⟩,
  ⟨80,.load8,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,22,7,9,0)⟩,
  ⟨80,.load8,0,1208925819614629174706175,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,22,7,9,1208925819614629174706175)⟩,
  ⟨80,.load8,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨80,.load8,1,1208925819614629174706175,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨80,.load8,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,22,7,9,0)⟩,
  ⟨80,.load8,6,1208925819614629174706175,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,22,7,9,1208925819614629174706175)⟩,
  ⟨80,.load16,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,46,7,9,0)⟩,
  ⟨80,.load16,0,1208925819614629174706175,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,46,7,9,1208925819614629174706175)⟩,
  ⟨80,.load16,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨80,.load16,1,1208925819614629174706175,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨80,.load16,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,46,7,9,0)⟩,
  ⟨80,.load16,6,1208925819614629174706175,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,46,7,9,1208925819614629174706175)⟩,
  ⟨80,.load32,0,0,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,44,7,9,0)⟩,
  ⟨80,.load32,0,1208925819614629174706175,7,9,([some 7,some 3,some 5,some 9],[some 5,some 7,some 9],[some 3,none],[some 3],[some 7,none,some 3],1,44,7,9,1208925819614629174706175)⟩,
  ⟨80,.load32,1,0,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨80,.load32,1,1208925819614629174706175,7,9,([some 3,some 3,some 5,some 9],[some 7,none,some 9],[some 3,none],[some 3],[some 3,none,none],0,0,7,5,0)⟩,
  ⟨80,.load32,6,0,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,44,7,9,0)⟩,
  ⟨80,.load32,6,1208925819614629174706175,7,9,([some 7,some 3,some 5,some 3],[some 5,some 7,some 9],[some 3,none],[some 3],[none,some 7,some 3],1,44,7,9,1208925819614629174706175)⟩,
  ⟨80,.store,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨80,.store,0,1208925819614629174706175,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,1208925819614629174706175)⟩,
  ⟨80,.store,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨80,.store,1,1208925819614629174706175,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,1208925819614629174706175)⟩,
  ⟨80,.store,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,0)⟩,
  ⟨80,.store,6,1208925819614629174706175,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,23,7,9,1208925819614629174706175)⟩,
  ⟨80,.store8,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨80,.store8,0,1208925819614629174706175,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,1208925819614629174706175)⟩,
  ⟨80,.store8,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨80,.store8,1,1208925819614629174706175,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,1208925819614629174706175)⟩,
  ⟨80,.store8,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,0)⟩,
  ⟨80,.store8,6,1208925819614629174706175,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,47,7,9,1208925819614629174706175)⟩,
  ⟨80,.store16,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨80,.store16,0,1208925819614629174706175,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,1208925819614629174706175)⟩,
  ⟨80,.store16,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨80,.store16,1,1208925819614629174706175,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,1208925819614629174706175)⟩,
  ⟨80,.store16,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,0)⟩,
  ⟨80,.store16,6,1208925819614629174706175,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,24,7,9,1208925819614629174706175)⟩,
  ⟨80,.store32,0,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨80,.store32,0,1208925819614629174706175,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,1208925819614629174706175)⟩,
  ⟨80,.store32,1,0,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨80,.store32,1,1208925819614629174706175,7,9,([none,some 3,some 5,some 9],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,1208925819614629174706175)⟩,
  ⟨80,.store32,6,0,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,0)⟩,
  ⟨80,.store32,6,1208925819614629174706175,7,9,([none,some 3,some 5,some 3],[some 5,none,some 9],[some 3,none],[some 3],[none,none,none],1,45,7,9,1208925819614629174706175)⟩]

private def nativeCheck (fixture : Fixture) : Bool :=
  if h : fixture.width = 0 then false else
    letI : NeZero fixture.width := ⟨h⟩
    let offset := BitVec.ofNat fixture.width fixture.offset
    nativeObservation fixture.operator fixture.destination offset
      (wordCse (nativeData fixture.mode fixture.operator offset)
        (.inst (HolInst.mem fixture.operator fixture.destination (.addr fixture.address offset)).toWordLangInst)) == fixture.expected

example : fixtures.all nativeCheck = true := by decide +kernel

private def checkExecuted (fixture : Fixture) (positive : fixture.width ≠ 0) : IO Bool :=
  letI : NeZero fixture.width := ⟨positive⟩
  do
    let offset := BitVec.ofNat fixture.width fixture.offset
    let observed := executedObservation fixture.operator fixture.destination offset
      (RiscV.wordCseProg (executedData fixture.mode fixture.operator offset)
        (.inst (executedMemoryInst fixture.operator fixture.destination fixture.address offset)))
    if observed != fixture.expected then
      IO.eprintln s!"FAIL executed CSE memory width={fixture.width} mode={fixture.mode} destination={fixture.destination} address={fixture.address} offset={fixture.offset}: {repr observed}"
      return false
    return true

def runChecks : IO Bool := do
  for fixture in fixtures do
    if h : fixture.width = 0 then
      IO.eprintln "FAIL CSE memory fixture has invalid zero width"
      return false
    else
      if !(← checkExecuted fixture h) then return false
  IO.println "PASS executed CSE memory: 256 original/kernel/runtime cases; all eight opcodes, five knowledge fields/full programs, guards, invalidation, hit/miss, canonical addresses and widths1/8/64/80"
  return true
end Flapjack.Test.WordCseProductionMemoryParity
