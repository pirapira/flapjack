import Flapjack.Compiler.Backend.WordCse.ProductionArithmetic

namespace Flapjack.Test.WordCseProductionArithmeticParity
open Flapjack RiscV Compiler.Backend.WordCse Compiler.Encoders.Asm
open Compiler.Backend.StackToLab

private abbrev Observation := List (Option Nat) × List (Option Nat) × List (Option Nat) ×
    List (Option Nat) × List (Option Nat) × Nat × List Nat × List Nat × List Nat
private structure Fixture where
  width : Nat
  kind : Nat
  mode : Nat
  destination : Nat
  expected : Observation
private def operation {width : Nat} [NeZero width] (kind destination : Nat) : HolArith width :=
  let immediate := BitVec.ofNat width (2^width-1)
  match kind with
  | 0 => .binop .add destination 9 (.reg 5)
  | 1 => .binop .sub destination 9 (.imm immediate)
  | 2 => .shift .lsl destination 9 (.reg 5)
  | 3 => .shift .lsr destination 9 (.imm immediate)
  | 4 => .div destination 9 5
  | 5 => .longMul destination 11 9 5
  | 6 => .longDiv destination 11 9 5 3
  | 7 => .addCarry destination 9 5 11
  | 8 => .addOverflow destination 9 5 11
  | _ => .subOverflow destination 9 5 11
private def canonicalEntries (mode : Nat) : List (Nat × Nat) :=
  [(3,3),(5,5),(9,if mode = 4 ∨ mode = 5 then 3 else 9)]
private def initialData (mode : Nat) : Knowledge :=
  { toCanonical := sptFromAList (canonicalEntries mode)
    toLatest := sptFromAList [(3,5),(9,9)]
    getsMem := [(.currHeap,3)]
    instrsMem := Misc.BalancedMap.insert listCmp [99] 3 Misc.BalancedMap.empty
    loadsMem := Misc.BalancedMap.insert listCmp [99] 3 Misc.BalancedMap.empty }
private def adjusted {width : Nat} [NeZero width] (mode : Nat) (op : HolArith width) :=
  canonicalArith (invalidateRegs (initialData mode) (arithWrites op)) op
private def factKey {width : Nat} [NeZero width] (mode : Nat) (op : HolArith width) : List Nat :=
  let a := adjusted mode op
  if (mode = 1 ∨ mode = 4) ∧ canMemArith a = true ∧ firstRegOfArith op ∉ arithReads a
  then instToNumList (.arith a) else [99]
private def nativeData {width : Nat} [NeZero width] (mode : Nat) (op : HolArith width) : Knowledge :=
  { initialData mode with
    instrsMem := Misc.BalancedMap.insert listCmp (factKey mode op) 3 Misc.BalancedMap.empty }
private def regMap (xs : List (Nat × Nat)) : WordCseRegMap :=
  xs.foldr (fun e m => m.insert e.1 e.2) ∅
private def executedData {width : Nat} [NeZero width] (mode : Nat) (op : HolArith width) : WordCseKnowledge :=
  { toCanonical := regMap (canonicalEntries mode)
    toLatest := regMap [(3,5),(9,9)]
    getsMem := regMap [(wordCseStoreCode (.currHeap : WordStore (BitVec width)),3)]
    instrsMem := (∅ : WordCseFactMap).insert (factKey mode op) 3
    loadsMem := (∅ : WordCseFactMap).insert [99] 3 }
private def nativeProgram {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) →
    Nat × List Nat × List Nat × List Nat
  | .inst (.arith a) =>
      let a := HolArith.ofWordLangArith a
      (1,arithToNumList a,arithWrites a,arithReads a)
  | .move priority [(r,current)] => (0,[priority],[r],[current])
  | _ => (2,[],[],[])
private def executedProgram {width : Nat} [NeZero width] : WordProg (BitVec width) →
    Nat × List Nat × List Nat × List Nat
  | .inst (.arith a) => match ExecutedCodec.arithFromExecuted? a with
      | some a => (1,arithToNumList a,arithWrites a,arithReads a)
      | none => (2,[],[],[])
  | .move priority [(r,current)] => (0,[priority],[r],[current])
  | _ => (2,[],[],[])
private def nativeObservation {width : Nat} [NeZero width] (mode : Nat) (op : HolArith width)
    (output : Knowledge × WordLangProgHOL (BitVec width)) : Observation :=
  let d := firstRegOfArith op
  let data := output.1
  ([d,3,5,9,11].map (fun k => sptLookup k data.toCanonical),
   [3,d,9,11].map (fun k => sptLookup k data.toLatest),
   [WordStore.currHeap,WordStore.nextFree].map (fun s => data.getsMem.lookup s),
   [instToNumList (.arith (adjusted mode op)),factKey mode op,[99]].map
     (fun k => Misc.BalancedMap.lookup listCmp k data.instrsMem),
   [[99]].map (fun k => Misc.BalancedMap.lookup listCmp k data.loadsMem),
   nativeProgram output.2)
private def executedObservation {width : Nat} [NeZero width] (mode : Nat) (op : HolArith width)
    (output : WordProg (BitVec width) × WordCseKnowledge) : Observation :=
  let d := firstRegOfArith op
  let data := output.2
  ([d,3,5,9,11].map (fun k => data.toCanonical[k]?),
   [3,d,9,11].map (fun k => data.toLatest[k]?),
   [WordStore.currHeap,WordStore.nextFree].map
     (fun s => data.getsMem[wordCseStoreCode (s : WordStore (BitVec width))]?),
   [instToNumList (.arith (adjusted mode op)),factKey mode op,[99]].map
     (fun k => data.instrsMem[k]?),
   [[99]].map (fun k => data.loadsMem[k]?),
   executedProgram output.1)
-- Numeric tuples strictly transcribed from original arithmetic_0..arithmetic_239.
private def fixtures : List Fixture := [
  ⟨1,0,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[7],[9, 5])⟩,
  ⟨1,0,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨1,0,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[2],[9, 5])⟩,
  ⟨1,0,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[25, 35, 109, 33, 105],[9],[9, 5])⟩,
  ⟨1,0,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨1,0,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[7],[9, 5])⟩,
  ⟨1,1,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 36, 109, 34, 1],[7],[9])⟩,
  ⟨1,1,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨1,1,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[25, 36, 109, 34, 1],[2],[9])⟩,
  ⟨1,1,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[25, 36, 109, 34, 1],[9],[9])⟩,
  ⟨1,1,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨1,1,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 36, 109, 34, 1],[7],[9])⟩,
  ⟨1,2,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨1,2,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨1,2,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[2],[9, 5])⟩,
  ⟨1,2,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[28, 40, 109, 33, 105],[9],[9, 5])⟩,
  ⟨1,2,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨1,2,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨1,3,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[28, 41, 109, 34, 1],[7],[9])⟩,
  ⟨1,3,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨1,3,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 41, 109, 34, 1],[2],[9])⟩,
  ⟨1,3,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[28, 41, 109, 34, 1],[9],[9])⟩,
  ⟨1,3,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨1,3,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[28, 41, 109, 34, 1],[7],[9])⟩,
  ⟨1,4,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[29, 109, 105],[7],[9, 5])⟩,
  ⟨1,4,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨1,4,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[29, 109, 105],[2],[9, 5])⟩,
  ⟨1,4,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[29, 109, 105],[9],[9, 5])⟩,
  ⟨1,4,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨1,4,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[29, 109, 105],[7],[9, 5])⟩,
  ⟨1,5,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨1,5,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨1,5,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[2, 11],[9, 5])⟩,
  ⟨1,5,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[26, 109, 105],[9, 11],[9, 5])⟩,
  ⟨1,5,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨1,5,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨1,6,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨1,6,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨1,6,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[2, 11],[9, 5, 3])⟩,
  ⟨1,6,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[27, 109, 105, 103],[9, 11],[9, 5, 3])⟩,
  ⟨1,6,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨1,6,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨1,7,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨1,7,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨1,7,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[2, 11],[9, 5, 11])⟩,
  ⟨1,7,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[30, 109, 105],[9, 11],[9, 5, 11])⟩,
  ⟨1,7,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨1,7,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨1,8,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨1,8,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨1,8,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[2, 11],[9, 5])⟩,
  ⟨1,8,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[31, 109, 105],[9, 11],[9, 5])⟩,
  ⟨1,8,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨1,8,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨1,9,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨1,9,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨1,9,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[2, 11],[9, 5])⟩,
  ⟨1,9,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[32, 109, 105],[9, 11],[9, 5])⟩,
  ⟨1,9,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨1,9,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,0,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[7],[9, 5])⟩,
  ⟨8,0,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨8,0,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[2],[9, 5])⟩,
  ⟨8,0,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[25, 35, 109, 33, 105],[9],[9, 5])⟩,
  ⟨8,0,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨8,0,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[7],[9, 5])⟩,
  ⟨8,1,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 36, 109, 34, 255],[7],[9])⟩,
  ⟨8,1,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨8,1,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[25, 36, 109, 34, 255],[2],[9])⟩,
  ⟨8,1,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[25, 36, 109, 34, 255],[9],[9])⟩,
  ⟨8,1,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨8,1,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 36, 109, 34, 255],[7],[9])⟩,
  ⟨8,2,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨8,2,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨8,2,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[2],[9, 5])⟩,
  ⟨8,2,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[28, 40, 109, 33, 105],[9],[9, 5])⟩,
  ⟨8,2,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨8,2,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨8,3,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[28, 41, 109, 34, 255],[7],[9])⟩,
  ⟨8,3,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨8,3,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 41, 109, 34, 255],[2],[9])⟩,
  ⟨8,3,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[28, 41, 109, 34, 255],[9],[9])⟩,
  ⟨8,3,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨8,3,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[28, 41, 109, 34, 255],[7],[9])⟩,
  ⟨8,4,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[29, 109, 105],[7],[9, 5])⟩,
  ⟨8,4,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨8,4,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[29, 109, 105],[2],[9, 5])⟩,
  ⟨8,4,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[29, 109, 105],[9],[9, 5])⟩,
  ⟨8,4,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨8,4,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[29, 109, 105],[7],[9, 5])⟩,
  ⟨8,5,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,5,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,5,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[2, 11],[9, 5])⟩,
  ⟨8,5,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[26, 109, 105],[9, 11],[9, 5])⟩,
  ⟨8,5,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,5,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,6,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨8,6,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨8,6,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[2, 11],[9, 5, 3])⟩,
  ⟨8,6,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[27, 109, 105, 103],[9, 11],[9, 5, 3])⟩,
  ⟨8,6,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨8,6,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨8,7,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨8,7,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨8,7,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[2, 11],[9, 5, 11])⟩,
  ⟨8,7,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[30, 109, 105],[9, 11],[9, 5, 11])⟩,
  ⟨8,7,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨8,7,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨8,8,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,8,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,8,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[2, 11],[9, 5])⟩,
  ⟨8,8,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[31, 109, 105],[9, 11],[9, 5])⟩,
  ⟨8,8,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,8,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,9,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,9,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,9,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[2, 11],[9, 5])⟩,
  ⟨8,9,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[32, 109, 105],[9, 11],[9, 5])⟩,
  ⟨8,9,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨8,9,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,0,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[7],[9, 5])⟩,
  ⟨64,0,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨64,0,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[2],[9, 5])⟩,
  ⟨64,0,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[25, 35, 109, 33, 105],[9],[9, 5])⟩,
  ⟨64,0,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨64,0,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[7],[9, 5])⟩,
  ⟨64,1,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 36, 109, 34, 18446744073709551615],[7],[9])⟩,
  ⟨64,1,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨64,1,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[25, 36, 109, 34, 18446744073709551615],[2],[9])⟩,
  ⟨64,1,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[25, 36, 109, 34, 18446744073709551615],[9],[9])⟩,
  ⟨64,1,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨64,1,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 36, 109, 34, 18446744073709551615],[7],[9])⟩,
  ⟨64,2,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨64,2,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨64,2,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[2],[9, 5])⟩,
  ⟨64,2,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[28, 40, 109, 33, 105],[9],[9, 5])⟩,
  ⟨64,2,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨64,2,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨64,3,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[28, 41, 109, 34, 18446744073709551615],[7],[9])⟩,
  ⟨64,3,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨64,3,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 41, 109, 34, 18446744073709551615],[2],[9])⟩,
  ⟨64,3,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[28, 41, 109, 34, 18446744073709551615],[9],[9])⟩,
  ⟨64,3,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨64,3,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[28, 41, 109, 34, 18446744073709551615],[7],[9])⟩,
  ⟨64,4,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[29, 109, 105],[7],[9, 5])⟩,
  ⟨64,4,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨64,4,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[29, 109, 105],[2],[9, 5])⟩,
  ⟨64,4,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[29, 109, 105],[9],[9, 5])⟩,
  ⟨64,4,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨64,4,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[29, 109, 105],[7],[9, 5])⟩,
  ⟨64,5,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,5,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,5,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[2, 11],[9, 5])⟩,
  ⟨64,5,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[26, 109, 105],[9, 11],[9, 5])⟩,
  ⟨64,5,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,5,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,6,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨64,6,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨64,6,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[2, 11],[9, 5, 3])⟩,
  ⟨64,6,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[27, 109, 105, 103],[9, 11],[9, 5, 3])⟩,
  ⟨64,6,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨64,6,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨64,7,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨64,7,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨64,7,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[2, 11],[9, 5, 11])⟩,
  ⟨64,7,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[30, 109, 105],[9, 11],[9, 5, 11])⟩,
  ⟨64,7,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨64,7,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨64,8,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,8,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,8,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[2, 11],[9, 5])⟩,
  ⟨64,8,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[31, 109, 105],[9, 11],[9, 5])⟩,
  ⟨64,8,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,8,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,9,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,9,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,9,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[2, 11],[9, 5])⟩,
  ⟨64,9,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[32, 109, 105],[9, 11],[9, 5])⟩,
  ⟨64,9,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨64,9,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,0,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[7],[9, 5])⟩,
  ⟨80,0,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨80,0,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[2],[9, 5])⟩,
  ⟨80,0,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[25, 35, 109, 33, 105],[9],[9, 5])⟩,
  ⟨80,0,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨80,0,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 35, 109, 33, 105],[7],[9, 5])⟩,
  ⟨80,1,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 36, 109, 34, 1208925819614629174706175],[7],[9])⟩,
  ⟨80,1,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨80,1,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[25, 36, 109, 34, 1208925819614629174706175],[2],[9])⟩,
  ⟨80,1,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[25, 36, 109, 34, 1208925819614629174706175],[9],[9])⟩,
  ⟨80,1,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨80,1,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[25, 36, 109, 34, 1208925819614629174706175],[7],[9])⟩,
  ⟨80,2,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨80,2,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨80,2,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[2],[9, 5])⟩,
  ⟨80,2,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[28, 40, 109, 33, 105],[9],[9, 5])⟩,
  ⟨80,2,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨80,2,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 40, 109, 33, 105],[7],[9, 5])⟩,
  ⟨80,3,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[28, 41, 109, 34, 1208925819614629174706175],[7],[9])⟩,
  ⟨80,3,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨80,3,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[28, 41, 109, 34, 1208925819614629174706175],[2],[9])⟩,
  ⟨80,3,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[28, 41, 109, 34, 1208925819614629174706175],[9],[9])⟩,
  ⟨80,3,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨80,3,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[28, 41, 109, 34, 1208925819614629174706175],[7],[9])⟩,
  ⟨80,4,0,7,([some 7, some 3, some 5, some 9, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[29, 109, 105],[7],[9, 5])⟩,
  ⟨80,4,1,7,([some 3, some 3, some 5, some 9, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨80,4,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[29, 109, 105],[2],[9, 5])⟩,
  ⟨80,4,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[29, 109, 105],[9],[9, 5])⟩,
  ⟨80,4,4,7,([some 3, some 3, some 5, some 3, none],[some 7, none, some 9, none],[some 3, none],[some 3, some 3, none],[some 3],0,[0],[7],[5])⟩,
  ⟨80,4,5,7,([some 7, some 3, some 5, some 3, none],[some 5, some 7, some 9, none],[some 3, none],[some 7, some 3, some 3],[some 3],1,[29, 109, 105],[7],[9, 5])⟩,
  ⟨80,5,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,5,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,5,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[2, 11],[9, 5])⟩,
  ⟨80,5,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[26, 109, 105],[9, 11],[9, 5])⟩,
  ⟨80,5,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,5,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[26, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,6,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨80,6,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨80,6,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[2, 11],[9, 5, 3])⟩,
  ⟨80,6,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[27, 109, 105, 103],[9, 11],[9, 5, 3])⟩,
  ⟨80,6,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨80,6,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[27, 109, 105, 103],[7, 11],[9, 5, 3])⟩,
  ⟨80,7,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨80,7,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨80,7,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[2, 11],[9, 5, 11])⟩,
  ⟨80,7,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[30, 109, 105],[9, 11],[9, 5, 11])⟩,
  ⟨80,7,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨80,7,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[30, 109, 105],[7, 11],[9, 5, 11])⟩,
  ⟨80,8,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,8,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,8,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[2, 11],[9, 5])⟩,
  ⟨80,8,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[31, 109, 105],[9, 11],[9, 5])⟩,
  ⟨80,8,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,8,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[31, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,9,0,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,9,1,7,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,9,2,2,([none, some 3, some 5, some 9, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[2, 11],[9, 5])⟩,
  ⟨80,9,3,9,([none, none, none, none, none],[none, none, none, none],[none, none],[none, none, none],[none],1,[32, 109, 105],[9, 11],[9, 5])⟩,
  ⟨80,9,4,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩,
  ⟨80,9,5,7,([none, some 3, some 5, some 3, none],[some 5, none, some 9, none],[some 3, none],[none, some 3, some 3],[some 3],1,[32, 109, 105],[7, 11],[9, 5])⟩ ]
private def nativeCheck (fixture : Fixture) : Bool :=
  if h : fixture.width = 0 then false else
    letI : NeZero fixture.width := ⟨h⟩
    let op := operation (width := fixture.width) fixture.kind fixture.destination
    nativeObservation fixture.mode op
      (wordCse (nativeData fixture.mode op) (.inst (HolInst.arith op).toWordLangInst)) == fixture.expected
example : fixtures.all nativeCheck = true := by decide +kernel
private def checkExecuted (fixture : Fixture) (positive : fixture.width ≠ 0) : IO Bool :=
  letI : NeZero fixture.width := ⟨positive⟩
  do
    let op := operation (width := fixture.width) fixture.kind fixture.destination
    let observed := executedObservation fixture.mode op
      (RiscV.wordCseProg (executedData fixture.mode op) (.inst (.arith (executedArithmetic op))))
    if observed != fixture.expected then
      IO.eprintln s!"FAIL executed CSE arithmetic width={fixture.width} kind={fixture.kind} mode={fixture.mode}: {repr observed}"
      return false
    return true
def runChecks : IO Bool := do
  for fixture in fixtures do
    if h : fixture.width = 0 then
      IO.eprintln "FAIL CSE arithmetic zero-width fixture"
      return false
    else
      if !(← checkExecuted fixture h) then return false
  IO.println "PASS executed CSE arithmetic: 240 original/kernel/runtime cases, all eight constructors, five knowledge fields, full payload encoding, guards, hit/miss and widths1/8/64/80"
  return true
end Flapjack.Test.WordCseProductionArithmeticParity
