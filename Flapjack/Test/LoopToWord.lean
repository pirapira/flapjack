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
def originalFromNumSetOrdered : List Nat := [3, 1, 2]
def originalFromNumSetDuplicate : List Nat := [3, 1, 2]
def originalMkNewCutsetEmpty : List Nat := [0]
def originalMkNewCutsetMapped : List Nat := [0, 6]
def originalMkNewCutsetDuplicate : List Nat := [0, 6]
def originalCompSkip : WordProg Nat := .skip
def originalCompAssignConst : WordProg Nat := .assign 6 (.const 7)
def originalCompSeqTick : WordProg Nat := .seq .skip .tick
def originalCompLoop : WordProg Nat :=
  .seq .tick (.seq (.loop [0, 6] .skip [0]) .tick)
def originalCompBreak : WordProg Nat := .break 2
def originalCompFail : WordProg Nat := .skip
def originalCompSetGlobal : WordProg Nat := .set (.temp 9) (.const 7)
def originalCompFuncSkip : WordProg Nat := .skip
def originalCompFuncAssign : WordProg Nat := .assign 4 (.const 3)
def originalCompFuncSeqAssign : WordProg Nat :=
  .seq (.assign 4 (.const 3)) (.assign 6 (.var 4))
def originalCompileProgEmpty : List (Nat × Nat × WordProg Nat) := []
def originalCompileProgSingleton : List (Nat × Nat × WordProg Nat) :=
  [(7, 2, .skip)]
def originalCompileProgTwo : List (Nat × Nat × WordProg Nat) :=
  [(7, 2, .skip), (8, 1, .assign 2 (.const 3))]
def originalCompileEmpty : List (Nat × Nat × WordProg Nat) := []
def originalCompileSingleton : List (Nat × Nat × WordProg Nat) :=
  [(7, 2, .skip)]

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

def sameWordProg : WordProg Nat → WordProg Nat → Bool
  | .skip, .skip => true
  | .assign leftName leftValue, .assign rightName rightValue =>
      leftName == rightName && sameWordExp leftValue rightValue
  | .inst left, .inst right => left == right
  | .set leftStore leftValue, .set rightStore rightValue =>
      sameWordStore leftStore rightStore && sameWordExp leftValue rightValue
  | .seq leftFirst leftSecond, .seq rightFirst rightSecond =>
      sameWordProg leftFirst rightFirst && sameWordProg leftSecond rightSecond
  | .loop leftIn leftBody leftOut, .loop rightIn rightBody rightOut =>
      leftIn == rightIn && sameWordProg leftBody rightBody && leftOut == rightOut
  | .break left, .break right => left == right
  | .tick, .tick => true
  | _, _ => false

def sameWordCode : List (Nat × Nat × WordProg Nat) →
    List (Nat × Nat × WordProg Nat) → Bool
  | [], [] => true
  | (leftName, leftArity, leftBody) :: leftRest,
      (rightName, rightArity, rightBody) :: rightRest =>
      leftName == rightName && leftArity == rightArity &&
        sameWordProg leftBody rightBody && sameWordCode leftRest rightRest
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
example : fromNumSet [] = [] := rfl
example : sameNatSet (fromNumSet (toNumSet [1, 2, 3]))
    originalFromNumSetOrdered := by decide
example : sameNatSet (fromNumSet (toNumSet [3, 1, 3, 2]))
    originalFromNumSetDuplicate := by decide
example : sameNatSet (mkNewCutset [(3, 6)] [])
    originalMkNewCutsetEmpty := by decide
example : sameNatSet (mkNewCutset [(3, 6)] [1, 2, 3])
    originalMkNewCutsetMapped := by decide
example : sameNatSet (mkNewCutset [(3, 6)] [3, 1, 3, 2])
    originalMkNewCutsetDuplicate := by decide

#guard sameWordProg (loopToWordProg ({ vars := [] } : WordContext)
    (.skip : LoopProg Nat)) originalCompSkip == true
#guard sameWordProg (loopToWordProg ({ vars := [(3, 6)] } : WordContext)
    (.assign 3 (.const 7) : LoopProg Nat)) originalCompAssignConst == true
#guard sameWordProg (loopToWordProg ({ vars := [] } : WordContext)
    (.seq .skip .tick : LoopProg Nat)) originalCompSeqTick == true
#guard sameWordProg (loopToWordProg ({ vars := [(3, 6)] } : WordContext)
    (.loop [3] .skip [] : LoopProg Nat)) originalCompLoop == true
#guard sameWordProg (loopToWordProg ({ vars := [] } : WordContext)
    (.break 2 : LoopProg Nat)) originalCompBreak == true
#guard sameWordProg (loopToWordProg ({ vars := [] } : WordContext)
    (.fail : LoopProg Nat)) originalCompFail == true
#guard sameWordProg (loopToWordProg ({ vars := [] } : WordContext)
    (.setGlobal 9 (.const 7) : LoopProg Nat)) originalCompSetGlobal == true
#guard sameWordProg (loopToWordCompFunc 7 [10] (.skip : LoopProg Nat))
    originalCompFuncSkip == true
#guard sameWordProg (loopToWordCompFunc 7 [10]
    (.assign 11 (.const 3) : LoopProg Nat)) originalCompFuncAssign == true
#guard sameWordProg (loopToWordCompFunc 7 [10]
    (.seq (.assign 11 (.const 3)) (.assign 12 (.var 11)) : LoopProg Nat))
    originalCompFuncSeqAssign == true
#guard sameWordCode (loopToWordCompileProg
    ([] : List (Nat × List Nat × LoopProg Nat))) originalCompileProgEmpty == true
#guard sameWordCode (loopToWordCompileProg
    ([(7, [10], .skip)] : List (Nat × List Nat × LoopProg Nat)))
    originalCompileProgSingleton == true
#guard sameWordCode (loopToWordCompileProg
    ([(7, [10], .skip), (8, [], .assign 11 (.const 3))] :
      List (Nat × List Nat × LoopProg Nat))) originalCompileProgTwo == true
#guard sameWordCode (loopToWordCompile
    ([] : List (Nat × List Nat × LoopProg Nat))) originalCompileEmpty == true
#guard sameWordCode (loopToWordCompile
    ([(7, [10], .skip)] : List (Nat × List Nat × LoopProg Nat)))
    originalCompileSingleton == true

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
  if !sameNatSet (fromNumSet (toNumSet [1, 2, 3]))
      originalFromNumSetOrdered then
    IO.println "FAIL LoopToWord.from_num_set ordered"; ok := false
  if !sameNatSet (fromNumSet (toNumSet [3, 1, 3, 2]))
      originalFromNumSetDuplicate then
    IO.println "FAIL LoopToWord.from_num_set duplicate"; ok := false
  if !sameNatSet (mkNewCutset [(3, 6)] []) originalMkNewCutsetEmpty then
    IO.println "FAIL LoopToWord.mk_new_cutset empty"; ok := false
  if !sameNatSet (mkNewCutset [(3, 6)] [1, 2, 3])
      originalMkNewCutsetMapped then
    IO.println "FAIL LoopToWord.mk_new_cutset mapped"; ok := false
  if !sameNatSet (mkNewCutset [(3, 6)] [3, 1, 3, 2])
      originalMkNewCutsetDuplicate then
    IO.println "FAIL LoopToWord.mk_new_cutset duplicate"; ok := false
  if !sameWordProg (loopToWordProg ({ vars := [] } : WordContext)
      (.skip : LoopProg Nat)) originalCompSkip then
    IO.println "FAIL LoopToWord.comp skip"; ok := false
  if !sameWordProg (loopToWordProg ({ vars := [(3, 6)] } : WordContext)
      (.assign 3 (.const 7) : LoopProg Nat)) originalCompAssignConst then
    IO.println "FAIL LoopToWord.comp assign"; ok := false
  if !sameWordProg (loopToWordProg ({ vars := [] } : WordContext)
      (.seq .skip .tick : LoopProg Nat)) originalCompSeqTick then
    IO.println "FAIL LoopToWord.comp sequence"; ok := false
  if !sameWordProg (loopToWordProg ({ vars := [(3, 6)] } : WordContext)
      (.loop [3] .skip [] : LoopProg Nat)) originalCompLoop then
    IO.println "FAIL LoopToWord.comp loop"; ok := false
  if !sameWordProg (loopToWordProg ({ vars := [] } : WordContext)
      (.break 2 : LoopProg Nat)) originalCompBreak then
    IO.println "FAIL LoopToWord.comp break"; ok := false
  if !sameWordProg (loopToWordProg ({ vars := [] } : WordContext)
      (.fail : LoopProg Nat)) originalCompFail then
    IO.println "FAIL LoopToWord.comp fail"; ok := false
  if !sameWordProg (loopToWordProg ({ vars := [] } : WordContext)
      (.setGlobal 9 (.const 7) : LoopProg Nat)) originalCompSetGlobal then
    IO.println "FAIL LoopToWord.comp set_global"; ok := false
  if !sameWordProg (loopToWordCompFunc 7 [10] (.skip : LoopProg Nat))
      originalCompFuncSkip then
    IO.println "FAIL LoopToWord.comp_func skip"; ok := false
  if !sameWordProg (loopToWordCompFunc 7 [10]
      (.assign 11 (.const 3) : LoopProg Nat)) originalCompFuncAssign then
    IO.println "FAIL LoopToWord.comp_func assign"; ok := false
  if !sameWordProg (loopToWordCompFunc 7 [10]
      (.seq (.assign 11 (.const 3)) (.assign 12 (.var 11)) : LoopProg Nat))
      originalCompFuncSeqAssign then
    IO.println "FAIL LoopToWord.comp_func sequence"; ok := false
  if !sameWordCode (loopToWordCompileProg
      ([] : List (Nat × List Nat × LoopProg Nat))) originalCompileProgEmpty then
    IO.println "FAIL LoopToWord.compile_prog empty"; ok := false
  if !sameWordCode (loopToWordCompileProg
      ([(7, [10], .skip)] : List (Nat × List Nat × LoopProg Nat)))
      originalCompileProgSingleton then
    IO.println "FAIL LoopToWord.compile_prog singleton"; ok := false
  if !sameWordCode (loopToWordCompileProg
      ([(7, [10], .skip), (8, [], .assign 11 (.const 3))] :
        List (Nat × List Nat × LoopProg Nat))) originalCompileProgTwo then
    IO.println "FAIL LoopToWord.compile_prog two"; ok := false
  if !sameWordCode (loopToWordCompile
      ([] : List (Nat × List Nat × LoopProg Nat))) originalCompileEmpty then
    IO.println "FAIL LoopToWord.compile empty"; ok := false
  if !sameWordCode (loopToWordCompile
      ([(7, [10], .skip)] : List (Nat × List Nat × LoopProg Nat)))
      originalCompileSingleton then
    IO.println "FAIL LoopToWord.compile singleton"; ok := false
  if ok then
    IO.println "PASS LoopToWord find_var/find_reg_imm/make_ctxt/comp_exp/to_num_set/from_num_set/mk_new_cutset/comp/comp_func/compile_prog/compile parity"
  pure ok

end Flapjack.Test.LoopToWord
