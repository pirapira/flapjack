import Flapjack.Compiler.Backend.WordCse.ProductionSet
import Flapjack.Compiler.Backend.WordCse.CanonicalArith
import Flapjack.Compiler.Backend.WordCse.CanonicalMove
import Flapjack.Compiler.Backend.WordCse.FactProducers
import Flapjack.Compiler.Backend.WordCse.Join

/-!
# `word_cse`: the common-subexpression transformation

Counterpart of `word_cseInst_def`, `word_cse_def`,
`word_common_subexp_elim_def` and `Seqs_def` of
`cakeml/compiler/backend/word_cseScript.sml` (446-646). The definitions are
written over the native CSE knowledge carrier and the faithful wordLang program
carrier.

HOL's `word_cseInst` consumes an `asm$inst` (`HolInst width`). The wordLang
program constructor `Inst` carries the reviewed constructor-for-constructor
mirror `WordLangInst (BitVec width)`. Every instruction this module emits is
the input instruction re-embedded by `HolInst.toWordLangInst`, and the `Inst`
clause of `word_cse` reads it back with `HolInst.ofWordLangInst`. These are
exact mutual inverses (`HolInst.to_of`, `HolInst.of_to`), so both transitions
return the original instruction unchanged. They are carrier infrastructure
only and change no clause. HOL's `EVEN r` is rendered `r % 2 = 0`, as in the
reviewed fact producers.
-/

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Compiler.Encoders.Asm

/-- Exact HOL `word_cseInst_def` (`word_cseScript.sml:446-479`): all five
    instruction clauses. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "word_cseInst_def"
  (words_as_type_indexed_bitvec)]
def wordCseInst {width : Nat} [NeZero width] (data : Knowledge) :
    HolInst width → Knowledge × WordLangProgHOL (BitVec width)
  | .skip => (data, .inst (HolInst.skip : HolInst width).toWordLangInst)
  | .const r w =>
      let data := invalidateData data r
      if r % 2 = 0 then (data, .inst (HolInst.const r w).toWordLangInst)
      else addToDataConst data r w
  | .arith a =>
      let r := firstRegOfArith a
      let data := invalidateRegs data (arithWrites a)
      let a' := canonicalArith data a
      let rds := arithReads a'
      if canMemArith a' = true ∧ r ∉ rds then
        addToData (registerReads data rds) r (.arith a') (.arith a)
      else (data, .inst (HolInst.arith a).toWordLangInst)
  | .mem op r (.addr a ofs) =>
      if isStore op then
        ({ data with loadsMem := Misc.BalancedMap.empty },
          .inst (HolInst.mem op r (.addr a ofs)).toWordLangInst)
      else
        let data := invalidateData data r
        if r % 2 = 0 ∨ a % 2 = 0 ∨ a = r then
          (data, .inst (HolInst.mem op r (.addr a ofs)).toWordLangInst)
        else
          let a' := canonicalRegs' r data a
          addToLoadAux (registerRead data a') r (loadToNumList op a' ofs)
            (.inst (HolInst.mem op r (.addr a ofs)).toWordLangInst)
  | .fp fp => (invalidateRegs data (fpWrites fp), .inst (HolInst.fp fp : HolInst width).toWordLangInst)

/-- Exact HOL `word_cse_def` (`word_cseScript.sml:538-632`): all twenty-six
    program clauses, by structural recursion on the program. The `Get` and
    `Set` clauses are the reviewed clause bodies `getClause`/`setClause`. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "word_cse_def"
  (words_as_type_indexed_bitvec)]
def wordCse {width : Nat} [NeZero width] (data : Knowledge) :
    WordLangProgHOL (BitVec width) → Knowledge × WordLangProgHOL (BitVec width)
  | .move r rs =>
      let data' := canonicalMoveRegs data rs
      (data', .move r rs)
  | .inst i =>
      let (data', p) := wordCseInst data (HolInst.ofWordLangInst i)
      (data', p)
  | .get r x => getClause data r x
  | .set x e => setClause data x e
  | .mustTerminate p =>
      let (data', p') := wordCse data p
      (data', .mustTerminate p')
  | .call ret dest args handler => (emptyData, .call ret dest args handler)
  | .seq p1 p2 =>
      let (data1, p1') := wordCse data p1
      let (data2, p2') := wordCse data1 p2
      (data2, .seq p1' p2')
  | .ite c r1 r2 p1 p2 =>
      let (data1, p1') := wordCse data p1
      let (data2, p2') := wordCse data p2
      (mergeData data1 data2, .ite c r1 r2 p1' p2')
  | .opCurrHeap b r1 r2 =>
      let data := invalidateData data r1
      if r2 % 2 = 0 ∨ r2 = r1 then (data, .opCurrHeap b r1 r2)
      else
        let r2' := canonicalRegs' r1 data r2
        let pL := opCurrHeapToNumList b r2'
        addToDataAux (registerRead data r2') r1 pL (.opCurrHeap b r1 r2)
  | .locValue r l =>
      let data := invalidateData data r
      addToDataAux data r [48, l] (.locValue r l)
  | .skip => (data, .skip)
  | .store e r => ({ data with loadsMem := Misc.BalancedMap.empty }, .store e r)
  | .assign r e => (data, .assign r e)
  | .raise r => (data, .raise r)
  | .return r1 r2 => (data, .return r1 r2)
  | .tick => (data, .tick)
  | .alloc r m => (emptyData, .alloc r m)
  | .install p l dp dl m => (emptyData, .install p l dp dl m)
  | .codeBufferWrite r1 r2 => (data, .codeBufferWrite r1 r2)
  | .dataBufferWrite r1 r2 => (data, .dataBufferWrite r1 r2)
  | .ffi s p1 l1 p2 l2 m => (emptyData, .ffi s p1 l1 p2 l2 m)
  | .storeConsts r1 r2 r3 r4 payload =>
      let data := invalidateRegs data [r1, r2, r3, r4]
      ({ data with loadsMem := Misc.BalancedMap.empty }, .storeConsts r1 r2 r3 r4 payload)
  | .shareInst op r exp =>
      let data := if isStore op then data else invalidateData data r
      (data, .shareInst op r exp)
  | .loop names c exitNames =>
      let (_, c') := wordCse emptyData c
      (emptyData, .loop names c' exitNames)
  | .break k => (data, .break k)
  | .continue k => (data, .continue k)

/-- Exact HOL `word_common_subexp_elim_def` (`word_cseScript.sml:634-638`). -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "word_common_subexp_elim_def"
  (words_as_type_indexed_bitvec)]
def wordCommonSubexpElim {width : Nat} [NeZero width] (prog : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) :=
  let (_, newProg) := wordCse emptyData prog
  newProg

/-- Exact HOL `Seqs_def` (`word_cseScript.sml:642-646`). -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "Seqs_def"]
def seqs {α : Type} : List (WordLangProgHOL α) → WordLangProgHOL α
  | [] => .skip
  | [x] => x
  | x :: y :: xs => .seq x (seqs (y :: xs))

end Flapjack.Compiler.Backend.WordCse
