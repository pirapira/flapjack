import Flapjack.LoopToWord
import Flapjack.Word

/-!
# Loop-to-word context lookup parity tests

These regressions exercise the ports of `find_var_def`, `find_reg_imm_def` and
`make_ctxt_def` from `cakeml/pancake/loop_to_wordScript.sml`. The expected
values below are checked-in output from the original HOL definitions, produced
by a direct invocation of `scripts/hol-probes/loop_to_word_probeScript.sml`.
This test therefore compares Flapjack with
the original Pancake implementation rather than with a second Lean
transcription.
-/

namespace Flapjack.Test.LoopToWord

open Flapjack Flapjack.LoopToWord

/-! The values are the literal records from
    `scripts/hol-probes/loop_to_word_probe.out`. Keep these names tied to the
    probe output: they are not executable reference definitions. -/
def originalFindVarEmpty : Nat := 0
def originalFindVarHit : Nat := 7
def originalFindVarMiss : Nat := 0
def originalFindVarCtxt10 : Nat := 2
def originalFindVarCtxt11 : Nat := 4
def originalFindVarCtxt12 : Nat := 6
def originalFindRegImmImm : RegImm Nat := .imm 5
def originalFindRegImmReg : RegImm Nat := .reg 0
def originalFindRegImmCtxt : RegImm Nat := .reg 4

/-! These expected expressions are the checked-in `comp_exp_def` outputs from
    the same HOL probe.  HOL uses 8-bit words in the representative expression
    cases; the Lean test uses `Nat` as the corresponding abstract word value. -/
def originalCompExpConst : WordExp Nat := .const 7
def originalCompExpVar : WordExp Nat := .var 6
def originalCompExpLookup : WordExp Nat := .lookup (.temp 9)
def originalCompExpBaseAddr : WordExp Nat := .lookup .currHeap
def originalCompExpTopAddr : WordExp Nat := .op .add
  [.lookup .currHeap,
   .shift .lsl (.lookup .heapLength) (.const 1)]
def originalCompExpNestedOp : WordExp Nat := .op .add [.const 1, .var 6]
def originalToNumSetOrdered : List Nat := [3, 1, 2]
def originalToNumSetDuplicate : List Nat := [3, 1, 2]

def sameRegImm : RegImm Nat → RegImm Nat → Bool
  | .imm left, .imm right => left == right
  | .reg left, .reg right => left == right
  | _, _ => false

def sameWordStore : WordStore Nat → WordStore Nat → Bool
  | .temp left, .temp right => left == right
  | .nextFree, .nextFree | .endOfHeap, .endOfHeap
  | .triggerGC, .triggerGC | .currHeap, .currHeap
  | .heapLength, .heapLength | .progStart, .progStart
  | .bitmapBase, .bitmapBase | .otherHeap, .otherHeap
  | .allocSize, .allocSize | .globals, .globals
  | .globReal, .globReal | .handler, .handler
  | .genStart, .genStart | .codeBuffer, .codeBuffer
  | .codeBufferEnd, .codeBufferEnd | .bitmapBuffer, .bitmapBuffer
  | .bitmapBufferEnd, .bitmapBufferEnd => true
  | _, _ => false

def sameWordExp : WordExp Nat → WordExp Nat → Bool
  | .const left, .const right => left == right
  | .var left, .var right => left == right
  | .lookup left, .lookup right => sameWordStore left right
  | .load left, .load right => sameWordExp left right
  | .op leftOp leftArgs, .op rightOp rightArgs =>
      leftOp == rightOp && sameWordExpList leftArgs rightArgs
  | .shift leftOp leftL leftR, .shift rightOp rightL rightR =>
      leftOp == rightOp && sameWordExp leftL rightL && sameWordExp leftR rightR
  | _, _ => false
where
  sameWordExpList : List (WordExp Nat) → List (WordExp Nat) → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        sameWordExp left right && sameWordExpList leftRest rightRest
    | _, _ => false

def sameOptionalWordExp : Option (WordExp Nat) → Option (WordExp Nat) → Bool
  | some left, some right => sameWordExp left right
  | none, none => true
  | _, _ => false

/-! `toAList` exposes the source sptree's implementation-dependent traversal
    order.  Compare the observable finite-set membership, not that traversal
    order, against the checked-in HOL records. -/
def sameNatSet (left right : List Nat) : Bool :=
  left.all (fun name => name ∈ right) && right.all (fun name => name ∈ left)

#guard findVar [] 0 == originalFindVarEmpty
#guard findVar [(3, 7)] 3 == originalFindVarHit
#guard findVar [(3, 7)] 4 == originalFindVarMiss
#guard findVar (makeCtxt 2 [10, 11, 12] []) 10 == originalFindVarCtxt10
#guard findVar (makeCtxt 2 [10, 11, 12] []) 11 == originalFindVarCtxt11
#guard findVar (makeCtxt 2 [10, 11, 12] []) 12 == originalFindVarCtxt12

example : findRegImm [] (.imm 5 : RegImm Nat) = originalFindRegImmImm := rfl
example : findRegImm [] (.reg 11 : RegImm Nat) = originalFindRegImmReg := rfl
example : findRegImm (makeCtxt 2 [10, 11, 12] []) (.reg 11 : RegImm Nat) =
    originalFindRegImmCtxt := rfl

example : wordCompileExp ({ vars := [] } : WordContext)
    (.const 7 : LoopExp Nat) = some originalCompExpConst := by
  simp [wordCompileExp, originalCompExpConst]
example : wordCompileExp ({ vars := [(3, 6)] } : WordContext)
    (.var 3 : LoopExp Nat) = some originalCompExpVar := by
  simp [wordCompileExp, wordFindVar, lookupNatInfo, originalCompExpVar]
example : wordCompileExp ({ vars := [] } : WordContext)
    (.lookup 9 : LoopExp Nat) = some originalCompExpLookup := by
  simp [wordCompileExp, originalCompExpLookup]
example : wordCompileExp ({ vars := [] } : WordContext)
    (.baseAddr : LoopExp Nat) = some originalCompExpBaseAddr := by
  simp [wordCompileExp, originalCompExpBaseAddr]
example : wordCompileExp ({ vars := [] } : WordContext)
    (.topAddr : LoopExp Nat) = some originalCompExpTopAddr := by
  simp [wordCompileExp, originalCompExpTopAddr]
example : wordCompileExp ({ vars := [(3, 6)] } : WordContext)
    (.op .add [.const 1, .var 3] : LoopExp Nat) =
    some originalCompExpNestedOp := by
  simp [wordCompileExp, wordCompileExp.wordCompileExpList, wordFindVar,
    lookupNatInfo, originalCompExpNestedOp]

example : toNumSet [] = [] := rfl
example : sameNatSet (toNumSet [1, 2, 3]) originalToNumSetOrdered := by decide
example : sameNatSet (toNumSet [3, 1, 3, 2]) originalToNumSetDuplicate := by decide

def runChecks : IO Bool := do
  let mut ok := true
  if findVar [] 0 != originalFindVarEmpty then
    IO.println "FAIL LoopToWord.findVar empty"; ok := false
  if findVar [(3, 7)] 3 != originalFindVarHit then
    IO.println "FAIL LoopToWord.findVar hit"; ok := false
  if findVar [(3, 7)] 4 != originalFindVarMiss then
    IO.println "FAIL LoopToWord.findVar miss"; ok := false
  if findVar (makeCtxt 2 [10, 11, 12] []) 10 != originalFindVarCtxt10 then
    IO.println "FAIL LoopToWord.makeCtxt/findVar 10"; ok := false
  if findVar (makeCtxt 2 [10, 11, 12] []) 11 != originalFindVarCtxt11 then
    IO.println "FAIL LoopToWord.makeCtxt/findVar 11"; ok := false
  if findVar (makeCtxt 2 [10, 11, 12] []) 12 != originalFindVarCtxt12 then
    IO.println "FAIL LoopToWord.makeCtxt/findVar 12"; ok := false
  if !sameRegImm (findRegImm [] (.imm 5 : RegImm Nat)) originalFindRegImmImm then
    IO.println "FAIL LoopToWord.findRegImm immediate"; ok := false
  if !sameRegImm (findRegImm [] (.reg 11 : RegImm Nat)) originalFindRegImmReg then
    IO.println "FAIL LoopToWord.findRegImm register"; ok := false
  if !sameRegImm (findRegImm (makeCtxt 2 [10, 11, 12] []) (.reg 11 : RegImm Nat))
      originalFindRegImmCtxt then
    IO.println "FAIL LoopToWord.findRegImm context"; ok := false
  if !sameOptionalWordExp (wordCompileExp ({ vars := [] } : WordContext)
      (.const 7 : LoopExp Nat)) (some originalCompExpConst) then
    IO.println "FAIL LoopToWord.comp_exp const"; ok := false
  if !sameOptionalWordExp (wordCompileExp ({ vars := [(3, 6)] } : WordContext)
      (.var 3 : LoopExp Nat)) (some originalCompExpVar) then
    IO.println "FAIL LoopToWord.comp_exp var"; ok := false
  if !sameOptionalWordExp (wordCompileExp ({ vars := [] } : WordContext)
      (.lookup 9 : LoopExp Nat)) (some originalCompExpLookup) then
    IO.println "FAIL LoopToWord.comp_exp lookup"; ok := false
  if !sameOptionalWordExp (wordCompileExp ({ vars := [] } : WordContext)
      (.baseAddr : LoopExp Nat)) (some originalCompExpBaseAddr) then
    IO.println "FAIL LoopToWord.comp_exp base address"; ok := false
  if !sameOptionalWordExp (wordCompileExp ({ vars := [] } : WordContext)
      (.topAddr : LoopExp Nat)) (some originalCompExpTopAddr) then
    IO.println "FAIL LoopToWord.comp_exp top address"; ok := false
  if !sameOptionalWordExp (wordCompileExp ({ vars := [(3, 6)] } : WordContext)
      (.op .add [.const 1, .var 3] : LoopExp Nat))
      (some originalCompExpNestedOp) then
    IO.println "FAIL LoopToWord.comp_exp nested op"; ok := false
  if !sameNatSet (toNumSet [1, 2, 3]) originalToNumSetOrdered then
    IO.println "FAIL LoopToWord.to_num_set ordered"; ok := false
  if !sameNatSet (toNumSet [3, 1, 3, 2]) originalToNumSetDuplicate then
    IO.println "FAIL LoopToWord.to_num_set duplicate"; ok := false
  if ok then
    IO.println "PASS LoopToWord find_var/find_reg_imm/make_ctxt/comp_exp/to_num_set parity"
  pure ok

end Flapjack.Test.LoopToWord
