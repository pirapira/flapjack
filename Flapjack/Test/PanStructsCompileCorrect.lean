import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect
import Flapjack.RiscV.Model
import Flapjack.Test.PanValueFfiSemantics

/-! Regression cases paired with
`scripts/hol-probes/pan_structs_compile_correct_probe.out` and
`scripts/hol-probes/pan_structs_compile_exp_correct_probe.out`. -/

namespace Flapjack.Test

open Flapjack

example :
    panStructConvertValue
      (.nStruct "Pair" [("left", .word 3), ("right", .word 5)]) =
        .rStruct [.word 3, .word 5] := by
  simp [panStructConvertValue, panStructConvertFieldValues]

example (context : StructPassContext) :
    structCompileProg context (.skip : Prog Nat) = .skip := by
  exact panStructCompileSkip_eq_skip context

private abbrev Word64 := Flapjack.RiscV.Word 64

def finiteMapRuntime : PanSemState Word64 (FfiState Unit) where
  locals := fun _ => none
  globals := fun _ => none
  structs := []
  code := []
  exceptionShapes := fun _ => none
  memory := fun _ => none
  memaddrs := fun _ => false
  sharedMemaddrs := fun _ => false
  clock := 3
  be := false
  ffi := statefulTestFfiState
  baseAddress := BitVec.ofNat 64 0
  topAddress := BitVec.ofNat 64 100

def finiteMapContext : StructPassContext where
  structs := []
  locals := [("local", .one)]
  globals := [("global", .one)]

def emptyStructCompileContext : StructPassContext where
  structs := []
  locals := []
  globals := []

def rstructCompileCaseExpressions : List (Exp Word64) :=
  [.const (BitVec.ofNat 64 3), .const (BitVec.ofNat 64 5)]

def rstructCompileCaseValue : PanValue Word64 :=
  .rStruct [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 5)]

/-! Paired concrete Load row for
    `compile_exp_correct_load=(Comb [One; One],Comb [One; One],T,T,T)` in
    `pan_structs_compile_exp_correct_probe.out`. -/
def loadCompileCaseRuntime : PanSemState Word64 (FfiState Unit) :=
  { finiteMapRuntime with
    memory := fun address =>
      if address == BitVec.ofNat 64 0 then some (.word (BitVec.ofNat 64 3))
      else if address == BitVec.ofNat 64 1 then some (.word (BitVec.ofNat 64 5))
      else none }

def loadCompileCaseValue : PanValue Word64 :=
  .rStruct [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 5)]

def loadCompileCaseExpression : Exp Word64 :=
  .load (.comb [.one, .one]) (.const (BitVec.ofNat 64 0))

example :
    structOldExpShape emptyStructCompileContext loadCompileCaseExpression =
        .comb [.one, .one] ∧
    panSemShapeOf loadCompileCaseValue = .comb [.one, .one] ∧
    panStructValueFieldsOkBool loadCompileCaseRuntime.structs loadCompileCaseValue = true ∧
    evalPanValueExp loadCompileCaseRuntime.structs loadCompileCaseRuntime.locals
      loadCompileCaseRuntime.globals loadCompileCaseRuntime.memory
      loadCompileCaseRuntime.baseAddress loadCompileCaseRuntime.topAddress
      (BitVec.ofNat 64 1) loadCompileCaseExpression = some loadCompileCaseValue ∧
    evalPanValueExp
      (panStructConvertState emptyStructCompileContext loadCompileCaseRuntime).structs
      (panStructConvertState emptyStructCompileContext loadCompileCaseRuntime).locals
      (panStructConvertState emptyStructCompileContext loadCompileCaseRuntime).globals
      (panStructConvertState emptyStructCompileContext loadCompileCaseRuntime).memory
      (panStructConvertState emptyStructCompileContext loadCompileCaseRuntime).baseAddress
      (panStructConvertState emptyStructCompileContext loadCompileCaseRuntime).topAddress
      (BitVec.ofNat 64 1)
        (structCompileExp emptyStructCompileContext loadCompileCaseExpression) =
        some (panStructConvertValue loadCompileCaseValue) := by
  simp [structOldExpShape, emptyStructCompileContext, loadCompileCaseExpression,
    loadCompileCaseValue, loadCompileCaseRuntime, finiteMapRuntime,
    panSemShapeOf, panStructValueFieldsOkBool, panStructValuesFieldsOkBool,
    evalPanValueExp,
    panValueFlatLoad, panValueFlatLoadFuel, panValueFlatLoadListFuel,
    panValueFlatReadWord, panValueFlatOffset, panValueFlatContextFuel,
    panValueFlatShapeFuel, panValueFlatShapeFuel.panValueFlatShapeListFuel,
    shapeSizeWithContext, isWfShape, isWfShape.isWfShapeList, panStructConvertState,
    panStructConvertValue, panStructConvertValues,
    structCompileExp, structCompileShape, structCompileShapeWF,
    structCompileShapeWF.structCompileShapesWF]

/-! Paired LoadByte constructor regression for the direct HOL-EVAL row
`compile_exp_correct_load_byte`. It calls the actual correctness case. -/
def loadByteCompileCaseRuntime : PanSemState Word64 (FfiState Unit) :=
  { finiteMapRuntime with
    memory := fun address =>
      if address == BitVec.ofNat 64 0 then some (.word (BitVec.ofNat 64 19))
      else none }

def loadByteCompileCaseExpression : Exp Word64 :=
  .loadByte (.const (BitVec.ofNat 64 0))

def loadByteCompileCaseValue : PanValue Word64 :=
  .word (BitVec.ofNat 64 19)

example :
    structOldExpShape (α := Word64) emptyStructCompileContext
      loadByteCompileCaseExpression = panSemShapeOf loadByteCompileCaseValue ∧
    panStructValueFieldsOkBool loadByteCompileCaseRuntime.structs
      loadByteCompileCaseValue = true ∧
    evalPanValueExp loadByteCompileCaseRuntime.structs
      loadByteCompileCaseRuntime.locals loadByteCompileCaseRuntime.globals
      loadByteCompileCaseRuntime.memory loadByteCompileCaseRuntime.baseAddress
      loadByteCompileCaseRuntime.topAddress (BitVec.ofNat 64 1)
      loadByteCompileCaseExpression = some loadByteCompileCaseValue ∧
    evalPanValueExp
      (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).structs
      (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).locals
      (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).globals
      (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).memory
      (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).baseAddress
      (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).topAddress
      (BitVec.ofNat 64 1)
      (structCompileExp emptyStructCompileContext loadByteCompileCaseExpression) =
        some (panStructConvertValue loadByteCompileCaseValue) := by
  have hload : evalPanValueExp loadByteCompileCaseRuntime.structs
      loadByteCompileCaseRuntime.locals loadByteCompileCaseRuntime.globals
      loadByteCompileCaseRuntime.memory loadByteCompileCaseRuntime.baseAddress
      loadByteCompileCaseRuntime.topAddress (BitVec.ofNat 64 1)
      loadByteCompileCaseExpression = some loadByteCompileCaseValue := by
    simp [loadByteCompileCaseRuntime, loadByteCompileCaseExpression,
      loadByteCompileCaseValue, finiteMapRuntime, evalPanValueExp]
  have hlocalsFields : panStructEveryValueFieldsOkBool
      loadByteCompileCaseRuntime.structs loadByteCompileCaseRuntime.locals := by
    intro name value hvalue
    simp [loadByteCompileCaseRuntime, finiteMapRuntime] at hvalue
  have hglobalsFields : panStructEveryValueFieldsOkBool
      loadByteCompileCaseRuntime.structs loadByteCompileCaseRuntime.globals := by
    intro name value hvalue
    simp [loadByteCompileCaseRuntime, finiteMapRuntime] at hvalue
  have hstructInfos : structInfosOk loadByteCompileCaseRuntime.structs := by
    simp [loadByteCompileCaseRuntime, finiteMapRuntime, structInfosOk]
  have hlocalsMap : panStructShapeMapEq emptyStructCompileContext.locals
      loadByteCompileCaseRuntime.locals := by
    intro name
    simp [emptyStructCompileContext, loadByteCompileCaseRuntime,
      finiteMapRuntime, lookupInfo]
  have hglobalsMap : panStructShapeMapEq emptyStructCompileContext.globals
      loadByteCompileCaseRuntime.globals := by
    intro name
    simp [emptyStructCompileContext, loadByteCompileCaseRuntime,
      finiteMapRuntime, lookupInfo]
  have haddressIH : ∀ addressValue,
      evalPanValueExp loadByteCompileCaseRuntime.structs
        loadByteCompileCaseRuntime.locals loadByteCompileCaseRuntime.globals
        loadByteCompileCaseRuntime.memory loadByteCompileCaseRuntime.baseAddress
        loadByteCompileCaseRuntime.topAddress (BitVec.ofNat 64 1)
        (.const (BitVec.ofNat 64 0)) = some addressValue →
      structOldExpShape emptyStructCompileContext (.const (BitVec.ofNat 64 0)) =
          panSemShapeOf addressValue ∧
      panStructValueFieldsOkBool loadByteCompileCaseRuntime.structs addressValue = true ∧
      evalPanValueExp
        (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).structs
        (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).locals
        (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).globals
        (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).memory
        (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext loadByteCompileCaseRuntime).topAddress
        (BitVec.ofNat 64 1)
        (structCompileExp emptyStructCompileContext (.const (BitVec.ofNat 64 0))) =
          some (panStructConvertValue addressValue) := by
    intro addressValue haddress
    have hword : addressValue = .word (BitVec.ofNat 64 0) := by
      simpa [evalPanValueExp] using haddress.symm
    subst addressValue
    refine ⟨by simp [structOldExpShape, panSemShapeOf], ?_, ?_⟩
    · simp [panStructValueFieldsOkBool]
    · simp [evalPanValueExp, panStructConvertState, panStructConvertValue]
  have hcase := panStructCompileExpCorrectLoadByteCase
    emptyStructCompileContext loadByteCompileCaseRuntime (BitVec.ofNat 64 1)
    (.const (BitVec.ofNat 64 0)) loadByteCompileCaseValue hload rfl
    hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap haddressIH
  exact ⟨hcase.1, hcase.2.1, hload, hcase.2.2⟩

/-! The direct HOL oracle row `compile_exp_correct_load32_le_success` uses an
aligned 64-bit word cell and checks that `Load32` extracts the low four bytes.
The same explicit RISC-V memory model is installed in the full evaluator on
both sides of the compile case; its default whole-cell fallback is not used. -/
def load32CompileCaseRuntime : PanSemState Word64 (FfiState Unit) :=
  { finiteMapRuntime with
    memory := fun address =>
      if address == BitVec.ofNat 64 8 then
        some (.word (BitVec.ofNat 64 0x8877665544332211))
      else none
    memaddrs := fun address => address == BitVec.ofNat 64 8 }

def load32CompileCaseMemoryAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel
    load32CompileCaseRuntime.memaddrs
    load32CompileCaseRuntime.sharedMemaddrs load32CompileCaseRuntime.be

def load32CompileCaseExpression : Exp Word64 :=
  .load32 (.const (BitVec.ofNat 64 8))

def load32CompileCaseValue : PanValue Word64 :=
  .word (BitVec.ofNat 64 0x44332211)

private theorem load32CompileCaseRead32 :
    load32CompileCaseMemoryAccess.read32
      load32CompileCaseMemoryAccess.domain
      (fun address => if address = BitVec.ofNat 64 8 then
        some (.word (BitVec.ofNat 64 0x8877665544332211)) else none)
      (BitVec.ofNat 64 8) (BitVec.ofNat 64 8) =
        some (BitVec.ofNat 64 0x44332211) := by
  decide

private theorem load32CompileCaseSourceEval :
    evalPanValueExpFull load32CompileCaseRuntime.structs
      load32CompileCaseRuntime.locals load32CompileCaseRuntime.globals
      load32CompileCaseRuntime.memory load32CompileCaseRuntime.baseAddress
      load32CompileCaseRuntime.topAddress (BitVec.ofNat 64 8)
      load32CompileCaseExpression
      (memoryAccess := some load32CompileCaseMemoryAccess) =
        some load32CompileCaseValue := by
  simp [evalPanValueExpFull, load32CompileCaseExpression,
    load32CompileCaseRuntime, finiteMapRuntime, load32CompileCaseRead32,
    load32CompileCaseValue]

example :
    structOldExpShape emptyStructCompileContext load32CompileCaseExpression = .one ∧
    panStructValueFieldsOkBool load32CompileCaseRuntime.structs
      load32CompileCaseValue = true ∧
    evalPanValueExpFull
      (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).structs
      (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).locals
      (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).globals
      (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).memory
      (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).baseAddress
      (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).topAddress
      (BitVec.ofNat 64 8)
      (structCompileExp emptyStructCompileContext load32CompileCaseExpression)
      (memoryAccess := some load32CompileCaseMemoryAccess) =
        some (panStructConvertValue load32CompileCaseValue) := by
  have hsource : evalPanValueExpFull load32CompileCaseRuntime.structs
      load32CompileCaseRuntime.locals load32CompileCaseRuntime.globals
      load32CompileCaseRuntime.memory load32CompileCaseRuntime.baseAddress
      load32CompileCaseRuntime.topAddress (BitVec.ofNat 64 8)
      load32CompileCaseExpression
      (memoryAccess := some load32CompileCaseMemoryAccess) =
        some load32CompileCaseValue := load32CompileCaseSourceEval
  have hlocalsFields : panStructEveryValueFieldsOkBool
      load32CompileCaseRuntime.structs load32CompileCaseRuntime.locals := by
    intro name value hvalue
    simp [load32CompileCaseRuntime, finiteMapRuntime] at hvalue
  have hglobalsFields : panStructEveryValueFieldsOkBool
      load32CompileCaseRuntime.structs load32CompileCaseRuntime.globals := by
    intro name value hvalue
    simp [load32CompileCaseRuntime, finiteMapRuntime] at hvalue
  have hstructInfos : structInfosOk load32CompileCaseRuntime.structs := by
    simp [load32CompileCaseRuntime, finiteMapRuntime, structInfosOk]
  have hlocalsMap : panStructShapeMapEq emptyStructCompileContext.locals
      load32CompileCaseRuntime.locals := by
    intro name
    simp [emptyStructCompileContext, load32CompileCaseRuntime,
      finiteMapRuntime, lookupInfo]
  have hglobalsMap : panStructShapeMapEq emptyStructCompileContext.globals
      load32CompileCaseRuntime.globals := by
    intro name
    simp [emptyStructCompileContext, load32CompileCaseRuntime,
      finiteMapRuntime, lookupInfo]
  have haddressIH : ∀ addressValue,
      evalPanValueExpFull load32CompileCaseRuntime.structs
        load32CompileCaseRuntime.locals load32CompileCaseRuntime.globals
        load32CompileCaseRuntime.memory load32CompileCaseRuntime.baseAddress
        load32CompileCaseRuntime.topAddress (BitVec.ofNat 64 8)
        (.const (BitVec.ofNat 64 8))
        (memoryAccess := some load32CompileCaseMemoryAccess) = some addressValue →
      structOldExpShape emptyStructCompileContext (.const (BitVec.ofNat 64 8)) =
          panSemShapeOf addressValue ∧
      panStructValueFieldsOkBool load32CompileCaseRuntime.structs addressValue = true ∧
      evalPanValueExpFull
        (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).structs
        (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).locals
        (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).globals
        (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).memory
        (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext load32CompileCaseRuntime).topAddress
        (BitVec.ofNat 64 8)
        (structCompileExp emptyStructCompileContext (.const (BitVec.ofNat 64 8)))
        (memoryAccess := some load32CompileCaseMemoryAccess) =
          some (panStructConvertValue addressValue) := by
    intro addressValue haddress
    have hword : addressValue = .word (BitVec.ofNat 64 8) := by
      simpa [evalPanValueExpFull] using haddress.symm
    subst addressValue
    exact ⟨by simp [structOldExpShape, panSemShapeOf],
      by simp [panStructValueFieldsOkBool],
      by simp [evalPanValueExpFull, panStructConvertState, panStructConvertValue]⟩
  have hcase := panStructCompileExpCorrectLoad32Case
    emptyStructCompileContext load32CompileCaseRuntime (BitVec.ofNat 64 8)
    load32CompileCaseMemoryAccess (.const (BitVec.ofNat 64 8))
    load32CompileCaseValue hsource rfl hlocalsFields hglobalsFields hstructInfos
    hlocalsMap hglobalsMap haddressIH
  simpa [load32CompileCaseExpression, load32CompileCaseValue,
    panSemShapeOf, panStructConvertValue] using hcase

/-! Recursive Panop/Mul specialization paired with the direct HOL-EVAL row
`compile_exp_correct_panop_mul`. -/
def panOpCompileCaseArguments : List (Exp Word64) :=
  [.const (BitVec.ofNat 64 3), .const (BitVec.ofNat 64 5)]

def panOpCompileCaseValue : PanValue Word64 :=
  .word (BitVec.ofNat 64 15)

example :
    structOldExpShape (α := Word64) emptyStructCompileContext
      (.panOp .mul panOpCompileCaseArguments) = panSemShapeOf panOpCompileCaseValue ∧
    panStructValueFieldsOkBool finiteMapRuntime.structs panOpCompileCaseValue = true ∧
    evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
      finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
      finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
      (.panOp .mul panOpCompileCaseArguments) = some panOpCompileCaseValue ∧
    evalPanValueExp
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
      (BitVec.ofNat 64 1)
      (structCompileExp emptyStructCompileContext (.panOp .mul panOpCompileCaseArguments)) =
        some (panStructConvertValue panOpCompileCaseValue) := by
  have hsource : evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
      finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
      finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
      (.panOp .mul panOpCompileCaseArguments) = some panOpCompileCaseValue := by
    simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, evalPanOp,
      panOpCompileCaseArguments,
      panOpCompileCaseValue, finiteMapRuntime]
  have hlocalsFields : panStructEveryValueFieldsOkBool
      finiteMapRuntime.structs finiteMapRuntime.locals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hglobalsFields : panStructEveryValueFieldsOkBool
      finiteMapRuntime.structs finiteMapRuntime.globals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hstructInfos : structInfosOk finiteMapRuntime.structs := by
    simp [finiteMapRuntime, structInfosOk]
  have hlocalsMap : panStructShapeMapEq emptyStructCompileContext.locals
      finiteMapRuntime.locals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have hglobalsMap : panStructShapeMapEq emptyStructCompileContext.globals
      finiteMapRuntime.globals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have harguments : ∀ argument, argument ∈ panOpCompileCaseArguments → ∀ subvalue,
      evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
        finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
        finiteMapRuntime.topAddress (BitVec.ofNat 64 1) argument = some subvalue →
      panStructContextShapeView emptyStructCompileContext.structs =
        panStructContextShapeView finiteMapRuntime.structs →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.locals →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.globals →
      structInfosOk finiteMapRuntime.structs →
      panStructShapeMapEq emptyStructCompileContext.locals finiteMapRuntime.locals →
      panStructShapeMapEq emptyStructCompileContext.globals finiteMapRuntime.globals →
      structOldExpShape emptyStructCompileContext argument = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs subvalue = true ∧
      evalPanValueExp
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
        (BitVec.ofNat 64 1) (structCompileExp emptyStructCompileContext argument) =
          some (panStructConvertValue subvalue) := by
    intro argument hmem subvalue heval _ _ _ _ _ _
    have harg : argument = .const (BitVec.ofNat 64 3) ∨
        argument = .const (BitVec.ofNat 64 5) := by
      simpa [panOpCompileCaseArguments] using hmem
    rcases harg with harg | harg
    · subst argument
      have hword : subvalue = .word (BitVec.ofNat 64 3) := by
        simpa [evalPanValueExp] using heval.symm
      subst subvalue
      exact ⟨by simp [structOldExpShape, panSemShapeOf],
        by simp [panStructValueFieldsOkBool],
        by simp [evalPanValueExp, panStructConvertState,
          panStructConvertValue]⟩
    · subst argument
      have hword : subvalue = .word (BitVec.ofNat 64 5) := by
        simpa [evalPanValueExp] using heval.symm
      subst subvalue
      exact ⟨by simp [structOldExpShape, panSemShapeOf],
        by simp [panStructValueFieldsOkBool],
        by simp [evalPanValueExp, panStructConvertState,
          panStructConvertValue]⟩
  have hcase := panStructCompileExpCorrectPanOpCase
    emptyStructCompileContext finiteMapRuntime (BitVec.ofNat 64 1) .mul
    panOpCompileCaseArguments panOpCompileCaseValue hsource rfl
    hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap harguments
  exact ⟨hcase.1, hcase.2.1, hsource, hcase.2.2⟩

/-! Recursive binary Cmp/Equal specialization paired with the direct
HOL-EVAL row `compile_exp_correct_cmp_equal`. -/
def cmpCompileCaseLeft : Exp Word64 := .const (BitVec.ofNat 64 3)
def cmpCompileCaseRight : Exp Word64 := .const (BitVec.ofNat 64 3)
def cmpCompileCaseValue : PanValue Word64 := .word (BitVec.ofNat 64 1)

example :
    structOldExpShape (α := Word64) emptyStructCompileContext
      (.cmp .equal cmpCompileCaseLeft cmpCompileCaseRight) =
        panSemShapeOf cmpCompileCaseValue ∧
    panStructValueFieldsOkBool finiteMapRuntime.structs cmpCompileCaseValue = true ∧
    evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
      finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
      finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
      (.cmp .equal cmpCompileCaseLeft cmpCompileCaseRight) = some cmpCompileCaseValue ∧
    evalPanValueExp
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
      (BitVec.ofNat 64 1)
      (structCompileExp emptyStructCompileContext
        (.cmp .equal cmpCompileCaseLeft cmpCompileCaseRight)) =
        some (panStructConvertValue cmpCompileCaseValue) := by
  have hsource : evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
      finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
      finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
      (.cmp .equal cmpCompileCaseLeft cmpCompileCaseRight) = some cmpCompileCaseValue := by
    simp [evalPanValueExp, evalPanCmp, cmpCompileCaseLeft, cmpCompileCaseRight,
      cmpCompileCaseValue, finiteMapRuntime]
  have hlocalsFields : panStructEveryValueFieldsOkBool
      finiteMapRuntime.structs finiteMapRuntime.locals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hglobalsFields : panStructEveryValueFieldsOkBool
      finiteMapRuntime.structs finiteMapRuntime.globals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hstructInfos : structInfosOk finiteMapRuntime.structs := by
    simp [finiteMapRuntime, structInfosOk]
  have hlocalsMap : panStructShapeMapEq emptyStructCompileContext.locals
      finiteMapRuntime.locals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have hglobalsMap : panStructShapeMapEq emptyStructCompileContext.globals
      finiteMapRuntime.globals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have hleft : ∀ subvalue,
      evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
        finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
        finiteMapRuntime.topAddress (BitVec.ofNat 64 1) cmpCompileCaseLeft = some subvalue →
      panStructContextShapeView emptyStructCompileContext.structs =
        panStructContextShapeView finiteMapRuntime.structs →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.locals →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.globals →
      structInfosOk finiteMapRuntime.structs →
      panStructShapeMapEq emptyStructCompileContext.locals finiteMapRuntime.locals →
      panStructShapeMapEq emptyStructCompileContext.globals finiteMapRuntime.globals →
      structOldExpShape emptyStructCompileContext cmpCompileCaseLeft =
        panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs subvalue = true ∧
      evalPanValueExp
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
        (BitVec.ofNat 64 1)
        (structCompileExp emptyStructCompileContext cmpCompileCaseLeft) =
          some (panStructConvertValue subvalue) := by
    intro subvalue heval _ _ _ _ _ _
    have hvalue : subvalue = .word (BitVec.ofNat 64 3) := by
      simpa [evalPanValueExp, cmpCompileCaseLeft] using heval.symm
    subst subvalue
    exact ⟨by simp [structOldExpShape, panSemShapeOf, cmpCompileCaseLeft],
      by simp [panStructValueFieldsOkBool],
      by simp [evalPanValueExp, panStructConvertState, panStructConvertValue,
        cmpCompileCaseLeft]⟩
  have hright : ∀ subvalue,
      evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
        finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
        finiteMapRuntime.topAddress (BitVec.ofNat 64 1) cmpCompileCaseRight = some subvalue →
      panStructContextShapeView emptyStructCompileContext.structs =
        panStructContextShapeView finiteMapRuntime.structs →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.locals →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.globals →
      structInfosOk finiteMapRuntime.structs →
      panStructShapeMapEq emptyStructCompileContext.locals finiteMapRuntime.locals →
      panStructShapeMapEq emptyStructCompileContext.globals finiteMapRuntime.globals →
      structOldExpShape emptyStructCompileContext cmpCompileCaseRight =
        panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs subvalue = true ∧
      evalPanValueExp
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
        (BitVec.ofNat 64 1)
        (structCompileExp emptyStructCompileContext cmpCompileCaseRight) =
          some (panStructConvertValue subvalue) := by
    intro subvalue heval _ _ _ _ _ _
    have hvalue : subvalue = .word (BitVec.ofNat 64 3) := by
      simpa [evalPanValueExp, cmpCompileCaseRight] using heval.symm
    subst subvalue
    exact ⟨by simp [structOldExpShape, panSemShapeOf, cmpCompileCaseRight],
      by simp [panStructValueFieldsOkBool],
      by simp [evalPanValueExp, panStructConvertState, panStructConvertValue,
        cmpCompileCaseRight]⟩
  have hcase := panStructCompileExpCorrectCmpCase
    emptyStructCompileContext finiteMapRuntime (BitVec.ofNat 64 1) .equal
    cmpCompileCaseLeft cmpCompileCaseRight cmpCompileCaseValue hsource rfl
    hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap hleft hright
  exact ⟨hcase.1, hcase.2.1, hsource, hcase.2.2⟩

/-! Recursive binary Shift/LSL specialization paired with the direct HOL-EVAL
row `compile_exp_correct_shift_lsl`. -/
def shiftCompileCaseLeft : Exp Word64 := .const (BitVec.ofNat 64 3)
def shiftCompileCaseRight : Exp Word64 := .const (BitVec.ofNat 64 1)
def shiftCompileCaseValue : PanValue Word64 := .word (BitVec.ofNat 64 6)

example :
    structOldExpShape (α := Word64) emptyStructCompileContext
      (.shift .lsl shiftCompileCaseLeft shiftCompileCaseRight) =
        panSemShapeOf shiftCompileCaseValue ∧
    panStructValueFieldsOkBool finiteMapRuntime.structs shiftCompileCaseValue = true ∧
    evalPanValueExpFull finiteMapRuntime.structs finiteMapRuntime.locals
      finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
      finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
      (.shift .lsl shiftCompileCaseLeft shiftCompileCaseRight) = some shiftCompileCaseValue ∧
    evalPanValueExpFull
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
      (BitVec.ofNat 64 1)
      (structCompileExp emptyStructCompileContext
        (.shift .lsl shiftCompileCaseLeft shiftCompileCaseRight)) =
        some (panStructConvertValue shiftCompileCaseValue) := by
  have hlsl : ShiftLeft.shiftLeft (BitVec.ofNat 64 3) (BitVec.ofNat 64 1) =
      BitVec.ofNat 64 6 := by decide
  have hvalid : PanShiftWidth.amount (α := Word64) (BitVec.ofNat 64 1) <
      PanShiftWidth.width (α := Word64) := by decide
  have hsource : evalPanValueExpFull finiteMapRuntime.structs finiteMapRuntime.locals
      finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
      finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
      (.shift .lsl shiftCompileCaseLeft shiftCompileCaseRight) =
        some shiftCompileCaseValue := by
    simp [evalPanValueExpFull, evalPanShiftFull, shiftCompileCaseLeft, shiftCompileCaseRight,
      shiftCompileCaseValue, finiteMapRuntime, hlsl, hvalid]
  have hlocalsFields : panStructEveryValueFieldsOkBool
      finiteMapRuntime.structs finiteMapRuntime.locals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hglobalsFields : panStructEveryValueFieldsOkBool
      finiteMapRuntime.structs finiteMapRuntime.globals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hstructInfos : structInfosOk finiteMapRuntime.structs := by
    simp [finiteMapRuntime, structInfosOk]
  have hlocalsMap : panStructShapeMapEq emptyStructCompileContext.locals
      finiteMapRuntime.locals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have hglobalsMap : panStructShapeMapEq emptyStructCompileContext.globals
      finiteMapRuntime.globals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have hleft : ∀ subvalue,
      evalPanValueExpFull finiteMapRuntime.structs finiteMapRuntime.locals
        finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
        finiteMapRuntime.topAddress (BitVec.ofNat 64 1) shiftCompileCaseLeft = some subvalue →
      panStructContextShapeView emptyStructCompileContext.structs =
        panStructContextShapeView finiteMapRuntime.structs →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.locals →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.globals →
      structInfosOk finiteMapRuntime.structs →
      panStructShapeMapEq emptyStructCompileContext.locals finiteMapRuntime.locals →
      panStructShapeMapEq emptyStructCompileContext.globals finiteMapRuntime.globals →
      structOldExpShape emptyStructCompileContext shiftCompileCaseLeft =
        panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs subvalue = true ∧
      evalPanValueExpFull
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
        (BitVec.ofNat 64 1)
        (structCompileExp emptyStructCompileContext shiftCompileCaseLeft) =
          some (panStructConvertValue subvalue) := by
    intro subvalue heval _ _ _ _ _ _
    have hvalue : subvalue = .word (BitVec.ofNat 64 3) := by
      simpa [evalPanValueExpFull, shiftCompileCaseLeft] using heval.symm
    subst subvalue
    exact ⟨by simp [structOldExpShape, panSemShapeOf, shiftCompileCaseLeft],
      by simp [panStructValueFieldsOkBool],
      by simp [evalPanValueExpFull, panStructConvertState, panStructConvertValue,
        shiftCompileCaseLeft]⟩
  have hright : ∀ subvalue,
      evalPanValueExpFull finiteMapRuntime.structs finiteMapRuntime.locals
        finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
        finiteMapRuntime.topAddress (BitVec.ofNat 64 1) shiftCompileCaseRight = some subvalue →
      panStructContextShapeView emptyStructCompileContext.structs =
        panStructContextShapeView finiteMapRuntime.structs →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.locals →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.globals →
      structInfosOk finiteMapRuntime.structs →
      panStructShapeMapEq emptyStructCompileContext.locals finiteMapRuntime.locals →
      panStructShapeMapEq emptyStructCompileContext.globals finiteMapRuntime.globals →
      structOldExpShape emptyStructCompileContext shiftCompileCaseRight =
        panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs subvalue = true ∧
      evalPanValueExpFull
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
        (BitVec.ofNat 64 1)
        (structCompileExp emptyStructCompileContext shiftCompileCaseRight) =
          some (panStructConvertValue subvalue) := by
    intro subvalue heval _ _ _ _ _ _
    have hvalue : subvalue = .word (BitVec.ofNat 64 1) := by
      simpa [evalPanValueExpFull, shiftCompileCaseRight] using heval.symm
    subst subvalue
    exact ⟨by simp [structOldExpShape, panSemShapeOf, shiftCompileCaseRight],
      by simp [panStructValueFieldsOkBool],
      by simp [evalPanValueExpFull, panStructConvertState, panStructConvertValue,
        shiftCompileCaseRight]⟩
  have hcase := panStructCompileExpCorrectShiftCase
    emptyStructCompileContext finiteMapRuntime (BitVec.ofNat 64 1) .lsl
    shiftCompileCaseLeft shiftCompileCaseRight shiftCompileCaseValue hsource rfl
    hlocalsFields hglobalsFields hstructInfos hlocalsMap hglobalsMap hleft hright
  exact ⟨hcase.1, hcase.2.1, hsource, hcase.2.2⟩

example : evalPanValueExpFull finiteMapRuntime.structs finiteMapRuntime.locals
    finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
    finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
    (.shift .asr (.const (BitVec.ofNat 64 0x8000000000000000))
      (.const (BitVec.ofNat 64 1))) =
    some (.word (BitVec.ofNat 64 0xc000000000000000)) := by
  have hvalid : PanShiftWidth.amount (α := Word64) (BitVec.ofNat 64 1) <
      PanShiftWidth.width (α := Word64) := by decide
  have hasr : ArithmeticShiftRight.arithmeticShiftRight
      (BitVec.ofNat 64 0x8000000000000000) (BitVec.ofNat 64 1) =
        BitVec.ofNat 64 0xc000000000000000 := by decide
  simp [evalPanValueExpFull, evalPanShiftFull, finiteMapRuntime, hvalid, hasr]

example : evalPanValueExpFull finiteMapRuntime.structs finiteMapRuntime.locals
    finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
    finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
    (.shift .ror (.const (BitVec.ofNat 64 0x8000000000000001))
      (.const (BitVec.ofNat 64 1))) =
    some (.word (BitVec.ofNat 64 0xc000000000000000)) := by
  have hvalid : PanShiftWidth.amount (α := Word64) (BitVec.ofNat 64 1) <
      PanShiftWidth.width (α := Word64) := by decide
  have hror : RotateRightOp.rotateRight
      (BitVec.ofNat 64 0x8000000000000001) (BitVec.ofNat 64 1) =
        BitVec.ofNat 64 0xc000000000000000 := by decide
  simp [evalPanValueExpFull, evalPanShiftFull, finiteMapRuntime, hvalid, hror]

example : evalPanValueExpFull finiteMapRuntime.structs finiteMapRuntime.locals
    finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
    finiteMapRuntime.topAddress (BitVec.ofNat 64 1)
    (.shift .lsl (.const (BitVec.ofNat 64 3))
      (.const (BitVec.ofNat 64 64))) = none := by
  have hcutoff : PanShiftWidth.amount (α := Word64) (BitVec.ofNat 64 64) ≠ 0 ∧
      PanShiftWidth.width (α := Word64) ≤
        PanShiftWidth.amount (α := Word64) (BitVec.ofNat 64 64) := by decide
  simp [evalPanValueExpFull, evalPanShiftFull, finiteMapRuntime, hcutoff]

/-! Direct Lean counterpart of the One and multiword Comb rows in
`pan_structs_mem_load_conversion_probe.out`. The conversion proof below uses
the same production fuel loader and the checked `size_of_compile_shape`
prerequisite used to preserve the second word's address. -/
def oneCombLoadShape : Shape := .comb [.one, .comb [.one, .one]]

def oneCombLoadReadWord (address : Word64) : Option Word64 :=
  if address == BitVec.ofNat 64 0 then some (BitVec.ofNat 64 7)
  else if address == BitVec.ofNat 64 1 then some (BitVec.ofNat 64 11)
  else if address == BitVec.ofNat 64 2 then some (BitVec.ofNat 64 13)
  else none

def oneCombLoadValue : PanValue Word64 :=
  .rStruct [.word (BitVec.ofNat 64 7),
    .rStruct [.word (BitVec.ofNat 64 11), .word (BitVec.ofNat 64 13)]]

example :
    panShapeHasNoNamed oneCombLoadShape = true ∧
    isWfShape [] oneCombLoadShape = true ∧
    panValueFlatLoadFuel [] oneCombLoadReadWord (BitVec.ofNat 64 1) 20
      oneCombLoadShape (BitVec.ofNat 64 0) = some oneCombLoadValue ∧
    panValueFlatLoadFuel [] oneCombLoadReadWord (BitVec.ofNat 64 1) 20
      (structCompileShapeWF [] oneCombLoadShape) (BitVec.ofNat 64 0) =
      some (panStructConvertValue oneCombLoadValue) := by
  have hshapeNames : panShapeHasNoNamed oneCombLoadShape = true := by
    rfl
  have hwf : isWfShape [] oneCombLoadShape = true := by
    simp [isWfShape, isWfShape.isWfShapeList, oneCombLoadShape]
  have hsource :
      panValueFlatLoadFuel [] oneCombLoadReadWord (BitVec.ofNat 64 1) 20
        oneCombLoadShape (BitVec.ofNat 64 0) = some oneCombLoadValue := by
    simp [panValueFlatLoadFuel, panValueFlatLoadListFuel, oneCombLoadShape,
      oneCombLoadReadWord, oneCombLoadValue, panValueFlatOffset,
      shapeSizeWithContext]
  have hconverted := panValueFlatLoadFuel_convert_one_comb
    [] (by simp [structInfosOk]) oneCombLoadReadWord (BitVec.ofNat 64 1)
    oneCombLoadShape hshapeNames hwf 20 (BitVec.ofNat 64 0) oneCombLoadValue hsource
  exact ⟨hshapeNames, hwf, hsource, hconverted⟩

/-! A nested named shape compiles to a nested `Comb`. This checks that the
    target loader's structural fuel covers every list element after alias
    expansion, while the source load walks the same three memory words. -/
def nestedLoadStructContext : StructContext :=
  [ ("Pair", {
      fields := [("inner", .named "Inner"), ("last", .one)]
      size := 3
    }),
    ("Inner", {
      fields := [("left", .one), ("right", .one)]
      size := 2
    }) ]

def nestedLoadCompileContext : StructPassContext :=
  { structs := nestedLoadStructContext, locals := [], globals := [] }

def nestedLoadRuntime : PanSemState Word64 (FfiState Unit) :=
  { finiteMapRuntime with
    structs := nestedLoadStructContext
    memory := fun address =>
      if address == BitVec.ofNat 64 0 then some (.word (BitVec.ofNat 64 7))
      else if address == BitVec.ofNat 64 1 then some (.word (BitVec.ofNat 64 11))
      else if address == BitVec.ofNat 64 2 then some (.word (BitVec.ofNat 64 13))
      else none }

def nestedLoadExpression : Exp Word64 :=
  .load (.named "Pair") (.const (BitVec.ofNat 64 0))

def nestedLoadSourceValue : PanValue Word64 :=
  .nStruct "Pair"
    [("inner", .nStruct "Inner"
      [("left", .word (BitVec.ofNat 64 7)), ("right", .word (BitVec.ofNat 64 11))]),
     ("last", .word (BitVec.ofNat 64 13))]

def nestedLoadConvertedValue : PanValue Word64 :=
  .rStruct [
    .rStruct [.word (BitVec.ofNat 64 7), .word (BitVec.ofNat 64 11)],
    .word (BitVec.ofNat 64 13)]

example :
    structOldExpShape nestedLoadCompileContext nestedLoadExpression = .named "Pair" ∧
    panSemShapeOf nestedLoadSourceValue = .named "Pair" ∧
    panStructValueFieldsOkBool nestedLoadRuntime.structs nestedLoadSourceValue = true ∧
    structCompileShapeWF nestedLoadStructContext (.named "Pair") =
      .comb [.comb [.one, .one], .one] ∧
    evalPanValueExp nestedLoadRuntime.structs nestedLoadRuntime.locals
      nestedLoadRuntime.globals nestedLoadRuntime.memory nestedLoadRuntime.baseAddress
      nestedLoadRuntime.topAddress (BitVec.ofNat 64 1) nestedLoadExpression =
      some nestedLoadSourceValue ∧
    evalPanValueExp [] nestedLoadRuntime.locals nestedLoadRuntime.globals
      nestedLoadRuntime.memory nestedLoadRuntime.baseAddress nestedLoadRuntime.topAddress
      (BitVec.ofNat 64 1)
      (structCompileExp nestedLoadCompileContext nestedLoadExpression) =
      some nestedLoadConvertedValue := by
  have hcompiled : structCompileShapeWF nestedLoadStructContext (.named "Pair") =
      .comb [.comb [.one, .one], .one] := by
    simp [structCompileShapeWF, structCompileShapeWF.structCompileShapesWF,
      nestedLoadStructContext, lookupInfoWithRest]
  constructor
  · simp [structOldExpShape, nestedLoadCompileContext, nestedLoadExpression]
  constructor
  · simp [panSemShapeOf, nestedLoadSourceValue]
  constructor
  · simp [panStructValueFieldsOkBool, panStructFieldValuesFieldsOkBool,
      nestedLoadRuntime, nestedLoadStructContext, nestedLoadSourceValue,
      panValueFieldsHaveShapes, panValueShape, panShapeMatches, lookupInfo]
  constructor
  · exact hcompiled
  constructor
  · simp [nestedLoadRuntime, nestedLoadStructContext, nestedLoadExpression,
      nestedLoadSourceValue, finiteMapRuntime, evalPanValueExp,
      panValueFlatLoad, panValueFlatLoadFuel, panValueFlatLoadFieldsFuel,
      panValueFlatReadWord, panValueFlatOffset,
      panValueFlatContextFuel, panValueFlatShapeFuel,
      panValueFlatFieldsFuel,
      shapeSizeWithContext, isWfShape, lookupInfoWithRest, lookupInfo]
  · have hcompiledExpression :
        structCompileExp nestedLoadCompileContext nestedLoadExpression =
          .load (.comb [.comb [.one, .one], .one]) (.const (BitVec.ofNat 64 0)) := by
      simp [structCompileExp, structCompileShape, nestedLoadCompileContext,
        nestedLoadExpression, hcompiled]
    rw [hcompiledExpression]
    simp [nestedLoadRuntime, nestedLoadStructContext, nestedLoadConvertedValue,
      finiteMapRuntime, evalPanValueExp, panValueFlatLoad, panValueFlatLoadFuel,
      panValueFlatLoadListFuel, panValueFlatReadWord, panValueFlatOffset,
      panValueFlatContextFuel, panValueFlatShapeFuel,
      panValueFlatShapeFuel.panValueFlatShapeListFuel, shapeSizeWithContext,
      isWfShape, isWfShape.isWfShapeList]

def nestedLoadReadWord (address : Word64) : Option Word64 :=
  panValueFlatReadWord nestedLoadRuntime.memory (BitVec.ofNat 64 1) none address

example :
    structInfosOk nestedLoadStructContext ∧
    isWfShape nestedLoadStructContext (.named "Pair") = true ∧
    panValueFlatLoadFuel nestedLoadStructContext nestedLoadReadWord
      (BitVec.ofNat 64 1) 20 (.named "Pair") (BitVec.ofNat 64 0) =
        some nestedLoadSourceValue ∧
    panValueFlatLoadFuel [] nestedLoadReadWord (BitVec.ofNat 64 1) 20
      (.comb [.comb [.one, .one], .one]) (BitVec.ofNat 64 0) =
        some nestedLoadConvertedValue ∧
    panStructValueFieldsOkBool nestedLoadStructContext nestedLoadSourceValue = true ∧
    shapeSizeWithContext [] (structCompileShapeWF nestedLoadStructContext (.named "Pair")) =
      shapeSizeWithContext nestedLoadStructContext (.named "Pair") ∧
    structOldExpShape nestedLoadCompileContext nestedLoadExpression =
      panSemShapeOf nestedLoadSourceValue ∧
    evalPanValueExp (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).structs
      (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).locals
      (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).globals
      (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).memory
      (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).baseAddress
      (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).topAddress
      (BitVec.ofNat 64 1)
      (structCompileExp nestedLoadCompileContext nestedLoadExpression) =
        some (panStructConvertValue nestedLoadSourceValue) := by
  have hok : structInfosOk nestedLoadStructContext := by
    let innerInfo : StructInfo := {
      fields := [("left", .one), ("right", .one)]
      size := 2
    }
    let pairInfo : StructInfo := {
      fields := [("inner", .named "Inner"), ("last", .one)]
      size := 3
    }
    have hinner : structInfosOk [("Inner", innerInfo)] := by
      apply structInfosOk_cons
      · simp [structInfosOk]
      · simp [innerInfo]
      · simp
      · intro shape hshape
        simp [innerInfo] at hshape
        rcases hshape with rfl | rfl <;> simp [isWfShape]
      · change (2 : Nat) = shapeSizeWithContext [] (.comb [.one, .one])
        simp [shapeSizeWithContext]
    change structInfosOk (("Pair", pairInfo) :: [("Inner", innerInfo)])
    apply structInfosOk_cons
    · exact hinner
    · simp [pairInfo]
    · simp
    · intro shape hshape
      simp [pairInfo] at hshape
      rcases hshape with hshape | hshape
      · rw [hshape]
        simp [isWfShape, lookupInfo]
      · rw [hshape]
        simp [isWfShape]
    · change (3 : Nat) = shapeSizeWithContext
        [("Inner", innerInfo)] (.comb [.named "Inner", .one])
      simp [shapeSizeWithContext, lookupInfo, innerInfo]
  have hwf : isWfShape nestedLoadStructContext (.named "Pair") = true := by
    simp [isWfShape, nestedLoadStructContext, lookupInfo]
  have hsourceFuel :
      panValueFlatContextFuel nestedLoadStructContext +
          panValueFlatShapeFuel (.named "Pair") + 1 ≤ 20 := by
    simp [nestedLoadStructContext, panValueFlatContextFuel,
      panValueFlatFieldsFuel, panValueFlatShapeFuel]
  have hcompiled : structCompileShapeWF nestedLoadStructContext (.named "Pair") =
      .comb [.comb [.one, .one], .one] := by
    simp [structCompileShapeWF, List.map_cons,
      structCompileShapeWF.structCompileShapesWF,
      nestedLoadStructContext, lookupInfoWithRest]
  have htargetFuel :
      panValueFlatShapeFuel
          (structCompileShapeWF nestedLoadStructContext (.named "Pair")) + 1 ≤ 20 := by
    rw [hcompiled]
    simp [panValueFlatShapeFuel, panValueFlatShapeFuel.panValueFlatShapeListFuel]
  have hsource :
      panValueFlatLoadFuel nestedLoadStructContext nestedLoadReadWord
        (BitVec.ofNat 64 1) 20 (.named "Pair") (BitVec.ofNat 64 0) =
          some nestedLoadSourceValue := by
    simp [panValueFlatLoadFuel, panValueFlatLoadFieldsFuel,
      nestedLoadReadWord, panValueFlatReadWord,
      nestedLoadRuntime, nestedLoadStructContext, nestedLoadSourceValue,
      finiteMapRuntime, panValueFlatOffset, shapeSizeWithContext,
      lookupInfoWithRest, lookupInfo]
  have hconverted := panValueFlatLoadFuel_convert_all
    (bytesInWord := BitVec.ofNat 64 1) (readWord := nestedLoadReadWord)
    nestedLoadStructContext 20 (.named "Pair") (BitVec.ofNat 64 0) 20
    nestedLoadSourceValue hok hwf hsourceFuel htargetFuel hsource
  have hloadShapeFields := panValueFlatLoadFuel_shape_fields
    (bytesInWord := BitVec.ofNat 64 1) (readWord := nestedLoadReadWord)
    nestedLoadStructContext 20 (.named "Pair") (BitVec.ofNat 64 0)
    nestedLoadSourceValue hok hwf hsource
  have hfields :
      panStructValueFieldsOkBool nestedLoadStructContext nestedLoadSourceValue = true :=
    hloadShapeFields.2
  have hsize := structCompileShapeWF_size nestedLoadStructContext (.named "Pair") hwf hok
  have hloadEval :
      evalPanValueExp nestedLoadRuntime.structs nestedLoadRuntime.locals
        nestedLoadRuntime.globals nestedLoadRuntime.memory nestedLoadRuntime.baseAddress
        nestedLoadRuntime.topAddress (BitVec.ofNat 64 1) nestedLoadExpression =
          some nestedLoadSourceValue := by
    simp [nestedLoadRuntime, nestedLoadStructContext, nestedLoadExpression,
      nestedLoadSourceValue, finiteMapRuntime, evalPanValueExp,
      panValueFlatLoad, panValueFlatLoadFuel, panValueFlatLoadFieldsFuel,
      panValueFlatReadWord, panValueFlatOffset, panValueFlatContextFuel,
      panValueFlatShapeFuel, panValueFlatFieldsFuel, shapeSizeWithContext,
      isWfShape, lookupInfoWithRest, lookupInfo]
  have hstructsView :
      panStructContextShapeView nestedLoadCompileContext.structs =
        panStructContextShapeView nestedLoadRuntime.structs := rfl
  have hlocalsFields : panStructEveryValueFieldsOkBool
      nestedLoadRuntime.structs nestedLoadRuntime.locals := by
    intro name value hvalue
    simp [nestedLoadRuntime, finiteMapRuntime] at hvalue
  have hglobalsFields : panStructEveryValueFieldsOkBool
      nestedLoadRuntime.structs nestedLoadRuntime.globals := by
    intro name value hvalue
    simp [nestedLoadRuntime, finiteMapRuntime] at hvalue
  have hlocalsMap : panStructShapeMapEq
      nestedLoadCompileContext.locals nestedLoadRuntime.locals := by
    intro name
    simp [nestedLoadCompileContext, nestedLoadRuntime, finiteMapRuntime, lookupInfo]
  have hglobalsMap : panStructShapeMapEq
      nestedLoadCompileContext.globals nestedLoadRuntime.globals := by
    intro name
    simp [nestedLoadCompileContext, nestedLoadRuntime, finiteMapRuntime, lookupInfo]
  have haddressIH : ∀ addressValue,
      evalPanValueExp nestedLoadRuntime.structs nestedLoadRuntime.locals
        nestedLoadRuntime.globals nestedLoadRuntime.memory
        nestedLoadRuntime.baseAddress nestedLoadRuntime.topAddress
        (BitVec.ofNat 64 1) (.const (BitVec.ofNat 64 0)) = some addressValue →
      structOldExpShape nestedLoadCompileContext (.const (BitVec.ofNat 64 0)) =
          panSemShapeOf addressValue ∧
      panStructValueFieldsOkBool nestedLoadRuntime.structs addressValue = true ∧
      evalPanValueExp (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).structs
        (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).locals
        (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).globals
        (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).memory
        (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).baseAddress
        (panStructConvertState nestedLoadCompileContext nestedLoadRuntime).topAddress
        (BitVec.ofNat 64 1)
        (structCompileExp nestedLoadCompileContext (.const (BitVec.ofNat 64 0))) =
          some (panStructConvertValue addressValue) := by
    intro addressValue heval
    have hword : addressValue = .word (BitVec.ofNat 64 0) := by
      simpa [evalPanValueExp] using heval.symm
    subst addressValue
    refine ⟨by simp [structOldExpShape, panSemShapeOf], ?_, ?_⟩
    · simp [panStructValueFieldsOkBool]
    · simp [evalPanValueExp, panStructConvertState, panStructConvertValue]
  have hloadCase := panStructCompileExpCorrectLoadCase
    nestedLoadCompileContext nestedLoadRuntime (BitVec.ofNat 64 1) (.named "Pair")
    (.const (BitVec.ofNat 64 0)) nestedLoadSourceValue hloadEval hstructsView
    hlocalsFields hglobalsFields hok hlocalsMap hglobalsMap haddressIH
  refine ⟨hok, hwf, hsource, ?_, hfields, ?_, ?_, ?_⟩
  · simpa [hcompiled, nestedLoadSourceValue, nestedLoadConvertedValue,
      panStructConvertValue, panStructConvertFieldValues, panStructConvertValues] using hconverted
  · simpa [hcompiled] using hsize
  · exact hloadCase.1
  · exact hloadCase.2.2

/-! The following leaf-case results pair with the BaseAddr, TopAddr, and
`BytesInWord` HOL-EVAL rows in `pan_structs_compile_exp_correct_probe.out`.
They invoke the actual three-premise/adapters `compile_exp_correct` cases. -/
example :
    (structOldExpShape (α := Word64) emptyStructCompileContext .baseAddr =
        panSemShapeOf (.word finiteMapRuntime.baseAddress) ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs
        (.word finiteMapRuntime.baseAddress) = true ∧
      evalPanValueExpFull
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
        (BitVec.ofNat 64 1) (structCompileExp emptyStructCompileContext .baseAddr)
        (memoryAccess := none) =
          some (panStructConvertValue (.word finiteMapRuntime.baseAddress))) ∧
    (structOldExpShape (α := Word64) emptyStructCompileContext .topAddr =
        panSemShapeOf (.word finiteMapRuntime.topAddress) ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs
        (.word finiteMapRuntime.topAddress) = true ∧
      evalPanValueExpFull
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
        (BitVec.ofNat 64 1) (structCompileExp emptyStructCompileContext .topAddr)
        (memoryAccess := none) =
          some (panStructConvertValue (.word finiteMapRuntime.topAddress))) ∧
    (structOldExpShape (α := Word64) emptyStructCompileContext .bytesInWord =
        panSemShapeOf (.word (BitVec.ofNat 64 1)) ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs
        (.word (BitVec.ofNat 64 1)) = true ∧
      evalPanValueExpFull
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
        (BitVec.ofNat 64 1) (structCompileExp emptyStructCompileContext .bytesInWord)
        (memoryAccess := none) =
          some (panStructConvertValue (.word (BitVec.ofNat 64 1)))) := by
  have hlocalsFields : panStructEveryValueFieldsOkBool
      finiteMapRuntime.structs finiteMapRuntime.locals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hglobalsFields : panStructEveryValueFieldsOkBool
      finiteMapRuntime.structs finiteMapRuntime.globals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hstructInfos : structInfosOk finiteMapRuntime.structs := by
    simp [finiteMapRuntime, structInfosOk]
  have hlocalsMap : panStructShapeMapEq emptyStructCompileContext.locals
      finiteMapRuntime.locals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have hglobalsMap : panStructShapeMapEq emptyStructCompileContext.globals
      finiteMapRuntime.globals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have hbase := panStructCompileExpCorrectBaseAddrCase emptyStructCompileContext
    finiteMapRuntime (BitVec.ofNat 64 1) none (.word finiteMapRuntime.baseAddress)
    (by simp [evalPanValueExpFull]) rfl hlocalsFields hglobalsFields
    hstructInfos hlocalsMap hglobalsMap
  have htop := panStructCompileExpCorrectTopAddrCase emptyStructCompileContext
    finiteMapRuntime (BitVec.ofNat 64 1) none (.word finiteMapRuntime.topAddress)
    (by simp [evalPanValueExpFull]) rfl hlocalsFields hglobalsFields
    hstructInfos hlocalsMap hglobalsMap
  have hbytes := panStructCompileExpCorrectBytesInWordCase emptyStructCompileContext
    finiteMapRuntime (BitVec.ofNat 64 1) none (.word (BitVec.ofNat 64 1))
    (by simp [evalPanValueExpFull]) rfl hlocalsFields hglobalsFields
    hstructInfos hlocalsMap hglobalsMap
  exact ⟨hbase, htop, hbytes⟩

example :
    structOldExpShape emptyStructCompileContext (.rStruct rstructCompileCaseExpressions) =
        .comb [.one, .one] ∧
    panStructValueFieldsOkBool finiteMapRuntime.structs rstructCompileCaseValue = true ∧
    evalPanValueExp
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
        (BitVec.ofNat 64 8)
        (structCompileExp emptyStructCompileContext (.rStruct rstructCompileCaseExpressions)) =
      some (.rStruct [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 5)]) := by
  have hsource : evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
      finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
      finiteMapRuntime.topAddress (BitVec.ofNat 64 8)
      (.rStruct rstructCompileCaseExpressions) = some rstructCompileCaseValue := by
    simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
      rstructCompileCaseExpressions, rstructCompileCaseValue]
  have hstructs : panStructContextShapeView emptyStructCompileContext.structs =
      panStructContextShapeView finiteMapRuntime.structs := by
    rfl
  have hlocalsFields : panStructEveryValueFieldsOkBool finiteMapRuntime.structs
      finiteMapRuntime.locals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hglobalsFields : panStructEveryValueFieldsOkBool finiteMapRuntime.structs
      finiteMapRuntime.globals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hstructInfos : structInfosOk finiteMapRuntime.structs := by
    simp [structInfosOk, finiteMapRuntime]
  have hlocalsMap : panStructShapeMapEq emptyStructCompileContext.locals
      finiteMapRuntime.locals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have hglobalsMap : panStructShapeMapEq emptyStructCompileContext.globals
      finiteMapRuntime.globals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have hconstant : ∀ word, ∀ subvalue,
      evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
        finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
        finiteMapRuntime.topAddress (BitVec.ofNat 64 8) (.const word) = some subvalue →
      panStructContextShapeView emptyStructCompileContext.structs =
        panStructContextShapeView finiteMapRuntime.structs →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.locals →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.globals →
      structInfosOk finiteMapRuntime.structs →
      panStructShapeMapEq emptyStructCompileContext.locals finiteMapRuntime.locals →
      panStructShapeMapEq emptyStructCompileContext.globals finiteMapRuntime.globals →
      structOldExpShape emptyStructCompileContext (.const word) = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs subvalue = true ∧
      evalPanValueExp
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
          (BitVec.ofNat 64 8)
          (structCompileExp emptyStructCompileContext (.const word)) =
        some (panStructConvertValue subvalue) := by
    intro word subvalue hevalSub _hstructs _hlocalsFields _hglobalsFields
      _hstructInfos _hlocalsMap _hglobalsMap
    simp [evalPanValueExp] at hevalSub
    cases hevalSub
    simp [structOldExpShape, panSemShapeOf, panStructValueFieldsOkBool,
      evalPanValueExp, panStructConvertState,
      panStructConvertValue, emptyStructCompileContext]
  have hinduction : PanStructAll (fun expression => ∀ subvalue,
      evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
        finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
        finiteMapRuntime.topAddress (BitVec.ofNat 64 8) expression = some subvalue →
      panStructContextShapeView emptyStructCompileContext.structs =
        panStructContextShapeView finiteMapRuntime.structs →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.locals →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.globals →
      structInfosOk finiteMapRuntime.structs →
      panStructShapeMapEq emptyStructCompileContext.locals finiteMapRuntime.locals →
      panStructShapeMapEq emptyStructCompileContext.globals finiteMapRuntime.globals →
      structOldExpShape emptyStructCompileContext expression = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs subvalue = true ∧
      evalPanValueExp
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
          (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
          (BitVec.ofNat 64 8) (structCompileExp emptyStructCompileContext expression) =
        some (panStructConvertValue subvalue)) rstructCompileCaseExpressions := by
    apply PanStructAll.cons
    · exact hconstant (BitVec.ofNat 64 3)
    · apply PanStructAll.cons
      · exact hconstant (BitVec.ofNat 64 5)
      · exact PanStructAll.nil
  have hcase := panStructCompileExpCorrectRStructCase emptyStructCompileContext
    finiteMapRuntime (BitVec.ofNat 64 8) rstructCompileCaseExpressions
    rstructCompileCaseValue hsource hstructs hlocalsFields hglobalsFields
    hstructInfos hlocalsMap hglobalsMap hinduction
  simpa [rstructCompileCaseExpressions, rstructCompileCaseValue,
    emptyStructCompileContext, finiteMapRuntime, panSemShapeOf,
    panStructValueFieldsOkBool, panStructValuesFieldsOkBool,
    panStructConvertValue, panStructConvertValues, evalPanValueExp,
    structCompileExp] using hcase

def pairCompileInfo : StructInfo where
  fields := [("left", .one), ("right", .one)]
  size := 2

def namedStructRuntime : PanSemState Word64 (FfiState Unit) :=
  { finiteMapRuntime with structs := [("Pair", pairCompileInfo)] }

def namedStructCompileContext : StructPassContext :=
  { emptyStructCompileContext with structs := [("Pair", pairCompileInfo)] }

def nstructCompileCaseFields : List (FieldName × Exp Word64) :=
  [("left", .const (BitVec.ofNat 64 3)),
   ("right", .const (BitVec.ofNat 64 5))]

def nstructCompileCaseValue : PanValue Word64 :=
  .nStruct "Pair"
    [("left", .word (BitVec.ofNat 64 3)),
     ("right", .word (BitVec.ofNat 64 5))]

example :
    structOldExpShape namedStructCompileContext
        (.nStruct "Pair" nstructCompileCaseFields) = .named "Pair" ∧
    panStructValueFieldsOkBool namedStructRuntime.structs nstructCompileCaseValue = true ∧
    evalPanValueExp
        (panStructConvertState namedStructCompileContext namedStructRuntime).structs
        (panStructConvertState namedStructCompileContext namedStructRuntime).locals
        (panStructConvertState namedStructCompileContext namedStructRuntime).globals
        (panStructConvertState namedStructCompileContext namedStructRuntime).memory
        (panStructConvertState namedStructCompileContext namedStructRuntime).baseAddress
        (panStructConvertState namedStructCompileContext namedStructRuntime).topAddress
        (BitVec.ofNat 64 8)
        (structCompileExp namedStructCompileContext
          (.nStruct "Pair" nstructCompileCaseFields)) =
      some (.rStruct [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 5)]) := by
  have hsource : evalPanValueExp namedStructRuntime.structs namedStructRuntime.locals
      namedStructRuntime.globals namedStructRuntime.memory namedStructRuntime.baseAddress
      namedStructRuntime.topAddress (BitVec.ofNat 64 8)
      (.nStruct "Pair" nstructCompileCaseFields) = some nstructCompileCaseValue := by
    have hfieldEval : evalPanValueExp.evalPanValueFields namedStructRuntime.structs
        namedStructRuntime.locals namedStructRuntime.globals namedStructRuntime.memory
        namedStructRuntime.baseAddress namedStructRuntime.topAddress (BitVec.ofNat 64 8)
        nstructCompileCaseFields = some
          [("left", .word (BitVec.ofNat 64 3)), ("right", .word (BitVec.ofNat 64 5))] := by
      simp [evalPanValueExp.evalPanValueFields, evalPanValueExp,
        nstructCompileCaseFields, namedStructRuntime, finiteMapRuntime]
    have hshapes : panValueFieldsHaveShapes
        [("Pair", pairCompileInfo)] pairCompileInfo.fields
        [("left", .word (BitVec.ofNat 64 3)), ("right", .word (BitVec.ofNat 64 5))] = true := by
      simp [panValueFieldsHaveShapes, panShapeMatches, panValueShape, pairCompileInfo]
    simp [evalPanValueExp, evalPanValueExp.evalPanValueFields,
      nstructCompileCaseFields, nstructCompileCaseValue, namedStructRuntime,
      lookupInfo, hshapes]
  have hstructs : panStructContextShapeView namedStructCompileContext.structs =
      panStructContextShapeView namedStructRuntime.structs := by
    rfl
  have hlocalsFields : panStructEveryValueFieldsOkBool namedStructRuntime.structs
      namedStructRuntime.locals := by
    intro name value hvalue
    simp [namedStructRuntime, finiteMapRuntime] at hvalue
  have hglobalsFields : panStructEveryValueFieldsOkBool namedStructRuntime.structs
      namedStructRuntime.globals := by
    intro name value hvalue
    simp [namedStructRuntime, finiteMapRuntime] at hvalue
  have hstructInfos : structInfosOk namedStructRuntime.structs := by
    refine ⟨?_, by simp [namedStructRuntime, finiteMapRuntime, pairCompileInfo], ?_, ?_⟩
    · intro entry hentry
      simp [namedStructRuntime, finiteMapRuntime, pairCompileInfo] at hentry
      subst entry
      simp
    · intro i name info hget shape hmem
      cases i with
      | zero =>
          simp only [namedStructRuntime, finiteMapRuntime,
            List.getElem?_cons_zero] at hget
          rcases hget with ⟨rfl, rfl⟩
          simp [pairCompileInfo] at hmem
          subst shape
          simp [isWfShape, namedStructRuntime, finiteMapRuntime]
      | succ i => simp [namedStructRuntime, finiteMapRuntime] at hget
    · intro entry hentry
      simp [namedStructRuntime, finiteMapRuntime, pairCompileInfo] at hentry
      subst entry
      simp [shapeSizeWithContext]
  have hlocalsMap : panStructShapeMapEq namedStructCompileContext.locals
      namedStructRuntime.locals := by
    intro name
    simp [namedStructCompileContext, emptyStructCompileContext,
      namedStructRuntime, finiteMapRuntime, lookupInfo]
  have hglobalsMap : panStructShapeMapEq namedStructCompileContext.globals
      namedStructRuntime.globals := by
    intro name
    simp [namedStructCompileContext, emptyStructCompileContext,
      namedStructRuntime, finiteMapRuntime, lookupInfo]
  have hconstant : ∀ word, ∀ subvalue,
      evalPanValueExp namedStructRuntime.structs namedStructRuntime.locals
        namedStructRuntime.globals namedStructRuntime.memory namedStructRuntime.baseAddress
        namedStructRuntime.topAddress (BitVec.ofNat 64 8) (.const word) = some subvalue →
      panStructContextShapeView namedStructCompileContext.structs =
        panStructContextShapeView namedStructRuntime.structs →
      panStructEveryValueFieldsOkBool namedStructRuntime.structs namedStructRuntime.locals →
      panStructEveryValueFieldsOkBool namedStructRuntime.structs namedStructRuntime.globals →
      structInfosOk namedStructRuntime.structs →
      panStructShapeMapEq namedStructCompileContext.locals namedStructRuntime.locals →
      panStructShapeMapEq namedStructCompileContext.globals namedStructRuntime.globals →
      structOldExpShape namedStructCompileContext (.const word) = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool namedStructRuntime.structs subvalue = true ∧
      evalPanValueExp (panStructConvertState namedStructCompileContext namedStructRuntime).structs
        (panStructConvertState namedStructCompileContext namedStructRuntime).locals
        (panStructConvertState namedStructCompileContext namedStructRuntime).globals
        (panStructConvertState namedStructCompileContext namedStructRuntime).memory
        (panStructConvertState namedStructCompileContext namedStructRuntime).baseAddress
        (panStructConvertState namedStructCompileContext namedStructRuntime).topAddress
        (BitVec.ofNat 64 8) (structCompileExp namedStructCompileContext (.const word)) =
          some (panStructConvertValue subvalue) := by
    intro word subvalue hevalSub _hstructs _hlocalsFields _hglobalsFields
      _hstructInfos _hlocalsMap _hglobalsMap
    cases subvalue with
    | word value =>
        have heq : word = value := by simpa [evalPanValueExp] using hevalSub
        subst value
        simp [structOldExpShape, panSemShapeOf, panStructValueFieldsOkBool,
          evalPanValueExp, panStructConvertState, panStructConvertValue,
          namedStructCompileContext]
    | rStruct values => simp [evalPanValueExp] at hevalSub
    | nStruct name values => simp [evalPanValueExp] at hevalSub
  have hinduction : PanStructAll (fun expression => ∀ subvalue,
      evalPanValueExp namedStructRuntime.structs namedStructRuntime.locals
        namedStructRuntime.globals namedStructRuntime.memory namedStructRuntime.baseAddress
        namedStructRuntime.topAddress (BitVec.ofNat 64 8) expression = some subvalue →
      panStructContextShapeView namedStructCompileContext.structs =
        panStructContextShapeView namedStructRuntime.structs →
      panStructEveryValueFieldsOkBool namedStructRuntime.structs namedStructRuntime.locals →
      panStructEveryValueFieldsOkBool namedStructRuntime.structs namedStructRuntime.globals →
      structInfosOk namedStructRuntime.structs →
      panStructShapeMapEq namedStructCompileContext.locals namedStructRuntime.locals →
      panStructShapeMapEq namedStructCompileContext.globals namedStructRuntime.globals →
      structOldExpShape namedStructCompileContext expression = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool namedStructRuntime.structs subvalue = true ∧
      evalPanValueExp (panStructConvertState namedStructCompileContext namedStructRuntime).structs
        (panStructConvertState namedStructCompileContext namedStructRuntime).locals
        (panStructConvertState namedStructCompileContext namedStructRuntime).globals
        (panStructConvertState namedStructCompileContext namedStructRuntime).memory
        (panStructConvertState namedStructCompileContext namedStructRuntime).baseAddress
        (panStructConvertState namedStructCompileContext namedStructRuntime).topAddress
        (BitVec.ofNat 64 8) (structCompileExp namedStructCompileContext expression) =
          some (panStructConvertValue subvalue))
      (nstructCompileCaseFields.map Prod.snd) := by
    apply PanStructAll.cons
    · exact hconstant (BitVec.ofNat 64 3)
    · apply PanStructAll.cons
      · exact hconstant (BitVec.ofNat 64 5)
      · exact PanStructAll.nil
  have hcase := panStructCompileExpCorrectNStructCase namedStructCompileContext
    namedStructRuntime (BitVec.ofNat 64 8) "Pair" nstructCompileCaseFields
    nstructCompileCaseValue hsource hstructs hlocalsFields hglobalsFields
    hstructInfos hlocalsMap hglobalsMap hinduction
  simpa [nstructCompileCaseFields, nstructCompileCaseValue,
    namedStructCompileContext, namedStructRuntime, pairCompileInfo,
    panSemShapeOf, panStructValueFieldsOkBool,
    panStructFieldValuesFieldsOkBool, panStructValuesFieldsOkBool,
    panStructConvertValue, panStructConvertFieldValues, evalPanValueExp,
    structCompileExp, structCompileExps_eq_map] using hcase

def nfieldCompileRuntime : PanSemState Word64 (FfiState Unit) :=
  { namedStructRuntime with
    locals := fun name => if name == "record" then some nstructCompileCaseValue else none }

def nfieldCompileContext : StructPassContext :=
  { namedStructCompileContext with locals := [("record", .named "Pair")] }

def nfieldCompileExpression : Exp Word64 :=
  .nField "right" (.var .local "record")

/-! Paired guard for the direct HOL-EVAL row
`compile_exp_correct_nfield=(One,One,T,T,T)` in
`scripts/hol-probes/pan_structs_compile_exp_correct_probe.out`. The Lean case
uses the full evaluator on source and converted states with no extra memory
model. -/
example :
    structOldExpShape nfieldCompileContext nfieldCompileExpression = .one ∧
    panStructValueFieldsOkBool nfieldCompileRuntime.structs
      (.word (BitVec.ofNat 64 5)) = true ∧
    evalPanValueExpFull
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).structs
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).locals
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).globals
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).memory
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).baseAddress
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).topAddress
        (BitVec.ofNat 64 8)
        (structCompileExp nfieldCompileContext nfieldCompileExpression)
        (memoryAccess := none) =
      some (.word (BitVec.ofNat 64 5)) := by
  have hsource : evalPanValueExpFull nfieldCompileRuntime.structs
      nfieldCompileRuntime.locals nfieldCompileRuntime.globals
      nfieldCompileRuntime.memory nfieldCompileRuntime.baseAddress
      nfieldCompileRuntime.topAddress (BitVec.ofNat 64 8)
      nfieldCompileExpression (memoryAccess := none) =
        some (.word (BitVec.ofNat 64 5)) := by
    simp [nfieldCompileExpression, nfieldCompileRuntime,
      nstructCompileCaseValue, finiteMapRuntime, namedStructRuntime,
      pairCompileInfo, evalPanValueExpFull, lookupInfo,
      lookupPanValueField]
  have hstructs : panStructContextShapeView nfieldCompileContext.structs =
      panStructContextShapeView nfieldCompileRuntime.structs := by
    rfl
  have hlocalsFields : panStructEveryValueFieldsOkBool nfieldCompileRuntime.structs
      nfieldCompileRuntime.locals := by
    intro name value hvalue
    by_cases hname : name = "record"
    · subst name
      have hvalueEq : value = nstructCompileCaseValue := by
        have hsome : some nstructCompileCaseValue = some value := by
          simpa [nfieldCompileRuntime] using hvalue
        exact (Option.some.inj hsome).symm
      subst value
      simp [panStructValueFieldsOkBool, nfieldCompileRuntime, namedStructRuntime,
        finiteMapRuntime, nstructCompileCaseValue, pairCompileInfo,
        panStructFieldValuesFieldsOkBool, lookupInfo,
        panValueFieldsHaveShapes, panShapeMatches, panValueShape]
    · simp [nfieldCompileRuntime] at hvalue
      rcases hvalue with ⟨heq, _⟩
      exact (hname heq).elim
  have hglobalsFields : panStructEveryValueFieldsOkBool nfieldCompileRuntime.structs
      nfieldCompileRuntime.globals := by
    intro name value hvalue
    simp [nfieldCompileRuntime, namedStructRuntime, finiteMapRuntime] at hvalue
  have hstructInfos : structInfosOk nfieldCompileRuntime.structs := by
    refine ⟨?_, by simp [nfieldCompileRuntime, namedStructRuntime, pairCompileInfo],
      ?_, ?_⟩
    · intro entry hentry
      simp [nfieldCompileRuntime, namedStructRuntime, pairCompileInfo] at hentry
      subst entry
      simp
    · intro i name info hget shape hmem
      cases i with
      | zero =>
          simp only [nfieldCompileRuntime, namedStructRuntime,
            List.getElem?_cons_zero] at hget
          rcases hget with ⟨rfl, rfl⟩
          simp [pairCompileInfo] at hmem
          subst shape
          simp [isWfShape, nfieldCompileRuntime, namedStructRuntime,
            finiteMapRuntime]
      | succ i => simp [nfieldCompileRuntime, namedStructRuntime] at hget
    · intro entry hentry
      simp [nfieldCompileRuntime, namedStructRuntime, pairCompileInfo] at hentry
      subst entry
      simp [shapeSizeWithContext]
  have hlocalsMap : panStructShapeMapEq nfieldCompileContext.locals
      nfieldCompileRuntime.locals := by
    intro name
    by_cases hname : name = "record"
    · subst name
      simp [nfieldCompileContext,
        namedStructCompileContext, emptyStructCompileContext,
        nfieldCompileRuntime, namedStructRuntime, pairCompileInfo,
        nstructCompileCaseValue, panSemShapeOf, lookupInfo]
    · have hneq : "record" ≠ name := by
        intro heq
        exact hname heq.symm
      simp [nfieldCompileContext,
        namedStructCompileContext, emptyStructCompileContext,
        nfieldCompileRuntime, namedStructRuntime, finiteMapRuntime,
        hname, hneq, lookupInfo]
  have hglobalsMap : panStructShapeMapEq nfieldCompileContext.globals
      nfieldCompileRuntime.globals := by
    intro name
    simp [nfieldCompileContext,
      namedStructCompileContext, emptyStructCompileContext,
      nfieldCompileRuntime, namedStructRuntime, finiteMapRuntime, lookupInfo]
  have hchildIH : ∀ subvalue,
      evalPanValueExpFull nfieldCompileRuntime.structs nfieldCompileRuntime.locals
        nfieldCompileRuntime.globals nfieldCompileRuntime.memory
        nfieldCompileRuntime.baseAddress nfieldCompileRuntime.topAddress
        (BitVec.ofNat 64 8) (.var .local "record")
        (memoryAccess := none) = some subvalue →
      panStructContextShapeView nfieldCompileContext.structs =
        panStructContextShapeView nfieldCompileRuntime.structs →
      panStructEveryValueFieldsOkBool nfieldCompileRuntime.structs
        nfieldCompileRuntime.locals →
      panStructEveryValueFieldsOkBool nfieldCompileRuntime.structs
        nfieldCompileRuntime.globals →
      structInfosOk nfieldCompileRuntime.structs →
      panStructShapeMapEq nfieldCompileContext.locals nfieldCompileRuntime.locals →
      panStructShapeMapEq nfieldCompileContext.globals nfieldCompileRuntime.globals →
      structOldExpShape nfieldCompileContext
        (.var .local "record" : Exp Word64) =
          panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool nfieldCompileRuntime.structs subvalue = true ∧
      evalPanValueExpFull
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).structs
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).locals
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).globals
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).memory
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).baseAddress
        (panStructConvertState nfieldCompileContext nfieldCompileRuntime).topAddress
        (BitVec.ofNat 64 8)
        (structCompileExp nfieldCompileContext (.var .local "record" : Exp Word64))
        (memoryAccess := none) =
          some (panStructConvertValue subvalue) := by
    intro subvalue hchild _ _ _ _ _ _
    have hvalueEq : subvalue = nstructCompileCaseValue := by
      have hsome : some nstructCompileCaseValue = some subvalue := by
        simpa [evalPanValueExpFull, nfieldCompileRuntime] using hchild
      exact (Option.some.inj hsome).symm
    subst subvalue
    refine ⟨?_, ?_, ?_⟩
    · simp [structOldExpShape, nfieldCompileContext,
        namedStructCompileContext, emptyStructCompileContext,
        nstructCompileCaseValue, panSemShapeOf, lookupInfo]
    · simp [panStructValueFieldsOkBool, nfieldCompileRuntime,
        namedStructRuntime, finiteMapRuntime, nstructCompileCaseValue, pairCompileInfo,
        panStructFieldValuesFieldsOkBool, lookupInfo, panValueFieldsHaveShapes,
        panShapeMatches, panValueShape]
    · simp [evalPanValueExpFull, structCompileExp, panStructConvertState,
        nfieldCompileRuntime, namedStructRuntime, nfieldCompileContext,
        namedStructCompileContext, emptyStructCompileContext,
        nstructCompileCaseValue, panStructConvertValue,
        panStructConvertFieldValues]
  have hcase := panStructCompileExpCorrectNFieldCase nfieldCompileContext
    nfieldCompileRuntime (BitVec.ofNat 64 8) none "right" (.var .local "record")
    (.word (BitVec.ofNat 64 5)) hsource hstructs hlocalsFields hglobalsFields
    hstructInfos hlocalsMap hglobalsMap hchildIH
  simpa [nfieldCompileExpression, nfieldCompileContext,
    namedStructCompileContext, emptyStructCompileContext,
    nfieldCompileRuntime, namedStructRuntime, finiteMapRuntime,
    nstructCompileCaseValue, pairCompileInfo, panSemShapeOf,
    panStructValueFieldsOkBool, panStructFieldValuesFieldsOkBool,
    panStructConvertState, panStructConvertValue, evalPanValueExpFull,
    structCompileExp, lookupInfo, lookupPanValueField,
    structFindFieldIndex] using hcase

#guard
  let source := evalPanValueExpFull
    nfieldCompileRuntime.structs nfieldCompileRuntime.locals
    nfieldCompileRuntime.globals nfieldCompileRuntime.memory
    nfieldCompileRuntime.baseAddress nfieldCompileRuntime.topAddress
    (BitVec.ofNat 64 8) nfieldCompileExpression (memoryAccess := none)
  let target := evalPanValueExpFull
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).structs
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).locals
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).globals
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).memory
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).baseAddress
    (panStructConvertState nfieldCompileContext nfieldCompileRuntime).topAddress
    (BitVec.ofNat 64 8)
    (structCompileExp nfieldCompileContext nfieldCompileExpression)
    (memoryAccess := none)
  panStructShapeEqBool
    (structOldExpShape nfieldCompileContext nfieldCompileExpression) .one &&
  panStructValueFieldsOkBool nfieldCompileRuntime.structs
    (.word (BitVec.ofNat 64 5)) &&
  (match source with
   | some (.word result) => result == BitVec.ofNat 64 5
   | _ => false) &&
  (match target with
   | some (.word result) => result == BitVec.ofNat 64 5
   | _ => false)

def rfieldCompileCaseValue : PanValue Word64 :=
  .rStruct [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 5)]

def rfieldCompileRuntime : PanSemState Word64 (FfiState Unit) :=
  { finiteMapRuntime with
    locals := fun name => if name == "tuple" then some rfieldCompileCaseValue else none }

def rfieldCompileContext : StructPassContext :=
  { emptyStructCompileContext with locals := [("tuple", .comb [.one, .one])] }

def rfieldCompileExpression : Exp Word64 :=
  .rField 1 (.var .local "tuple")

/-! Paired guard for the direct HOL-EVAL row
`compile_exp_correct_rfield=(One,One,T,T,T)` in
`scripts/hol-probes/pan_structs_compile_exp_correct_probe.out`. The Lean case
uses the full evaluator on source and converted states with no extra memory
model. -/
example :
    structOldExpShape rfieldCompileContext rfieldCompileExpression = .one ∧
    panStructValueFieldsOkBool rfieldCompileRuntime.structs
      (.word (BitVec.ofNat 64 5)) = true ∧
    evalPanValueExpFull
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).structs
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).locals
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).globals
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).memory
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).baseAddress
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).topAddress
        (BitVec.ofNat 64 8)
        (structCompileExp rfieldCompileContext rfieldCompileExpression)
        (memoryAccess := none) =
      some (.word (BitVec.ofNat 64 5)) := by
  have hsource : evalPanValueExpFull rfieldCompileRuntime.structs
      rfieldCompileRuntime.locals rfieldCompileRuntime.globals
      rfieldCompileRuntime.memory rfieldCompileRuntime.baseAddress
      rfieldCompileRuntime.topAddress (BitVec.ofNat 64 8)
      rfieldCompileExpression (memoryAccess := none) =
        some (.word (BitVec.ofNat 64 5)) := by
    simp [rfieldCompileExpression, rfieldCompileRuntime,
      rfieldCompileCaseValue, finiteMapRuntime, evalPanValueExpFull]
  have hstructs : panStructContextShapeView rfieldCompileContext.structs =
      panStructContextShapeView rfieldCompileRuntime.structs := by
    rfl
  have hlocalsFields : panStructEveryValueFieldsOkBool rfieldCompileRuntime.structs
      rfieldCompileRuntime.locals := by
    intro name value hvalue
    by_cases hname : name = "tuple"
    · subst name
      have hvalueEq : value = rfieldCompileCaseValue := by
        have hsome : some rfieldCompileCaseValue = some value := by
          simpa [rfieldCompileRuntime] using hvalue
        exact (Option.some.inj hsome).symm
      subst value
      simp [panStructValueFieldsOkBool, panStructValuesFieldsOkBool,
        rfieldCompileRuntime, finiteMapRuntime, rfieldCompileCaseValue]
    · simp [rfieldCompileRuntime] at hvalue
      rcases hvalue with ⟨heq, _⟩
      exact (hname heq).elim
  have hglobalsFields : panStructEveryValueFieldsOkBool rfieldCompileRuntime.structs
      rfieldCompileRuntime.globals := by
    intro name value hvalue
    simp [rfieldCompileRuntime, finiteMapRuntime] at hvalue
  have hstructInfos : structInfosOk rfieldCompileRuntime.structs := by
    simp [structInfosOk, rfieldCompileRuntime, finiteMapRuntime]
  have hlocalsMap : panStructShapeMapEq rfieldCompileContext.locals
      rfieldCompileRuntime.locals := by
    intro name
    by_cases hname : name = "tuple"
    · subst name
      simp [rfieldCompileContext, emptyStructCompileContext,
        rfieldCompileRuntime, finiteMapRuntime, rfieldCompileCaseValue,
        panSemShapeOf, lookupInfo]
    · have hneq : "tuple" ≠ name := by
        intro heq
        exact hname heq.symm
      simp [rfieldCompileContext, emptyStructCompileContext,
        rfieldCompileRuntime, finiteMapRuntime, hname, hneq, lookupInfo]
  have hglobalsMap : panStructShapeMapEq rfieldCompileContext.globals
      rfieldCompileRuntime.globals := by
    intro name
    simp [rfieldCompileContext, emptyStructCompileContext,
      rfieldCompileRuntime, finiteMapRuntime, lookupInfo]
  have hchildIH : ∀ subvalue,
      evalPanValueExpFull rfieldCompileRuntime.structs rfieldCompileRuntime.locals
        rfieldCompileRuntime.globals rfieldCompileRuntime.memory
        rfieldCompileRuntime.baseAddress rfieldCompileRuntime.topAddress
        (BitVec.ofNat 64 8) (.var .local "tuple")
        (memoryAccess := none) = some subvalue →
      panStructContextShapeView rfieldCompileContext.structs =
        panStructContextShapeView rfieldCompileRuntime.structs →
      panStructEveryValueFieldsOkBool rfieldCompileRuntime.structs
        rfieldCompileRuntime.locals →
      panStructEveryValueFieldsOkBool rfieldCompileRuntime.structs
        rfieldCompileRuntime.globals →
      structInfosOk rfieldCompileRuntime.structs →
      panStructShapeMapEq rfieldCompileContext.locals rfieldCompileRuntime.locals →
      panStructShapeMapEq rfieldCompileContext.globals rfieldCompileRuntime.globals →
      structOldExpShape rfieldCompileContext
        (.var .local "tuple" : Exp Word64) = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool rfieldCompileRuntime.structs subvalue = true ∧
      evalPanValueExpFull
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).structs
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).locals
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).globals
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).memory
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).baseAddress
        (panStructConvertState rfieldCompileContext rfieldCompileRuntime).topAddress
        (BitVec.ofNat 64 8)
        (structCompileExp rfieldCompileContext (.var .local "tuple" : Exp Word64))
        (memoryAccess := none) =
          some (panStructConvertValue subvalue) := by
    intro subvalue hchild _ _ _ _ _ _
    have hvalueEq : subvalue = rfieldCompileCaseValue := by
      have hsome : some rfieldCompileCaseValue = some subvalue := by
        simpa [evalPanValueExpFull, rfieldCompileRuntime] using hchild
      exact (Option.some.inj hsome).symm
    subst subvalue
    refine ⟨?_, ?_, ?_⟩
    · simp [structOldExpShape, rfieldCompileContext,
        emptyStructCompileContext, rfieldCompileCaseValue, panSemShapeOf, lookupInfo]
    · simp [panStructValueFieldsOkBool, panStructValuesFieldsOkBool,
        rfieldCompileRuntime, finiteMapRuntime, rfieldCompileCaseValue]
    · simp [evalPanValueExpFull, structCompileExp, panStructConvertState,
        rfieldCompileRuntime, finiteMapRuntime, rfieldCompileContext,
        emptyStructCompileContext, rfieldCompileCaseValue, panStructConvertValue,
        panStructConvertValues]
  have hcase := panStructCompileExpCorrectRFieldCase rfieldCompileContext
    rfieldCompileRuntime (BitVec.ofNat 64 8) none 1 (.var .local "tuple")
    (.word (BitVec.ofNat 64 5)) hsource hstructs hlocalsFields hglobalsFields
    hstructInfos hlocalsMap hglobalsMap hchildIH
  simpa [rfieldCompileExpression, rfieldCompileContext,
    emptyStructCompileContext, rfieldCompileRuntime, finiteMapRuntime,
    rfieldCompileCaseValue, panSemShapeOf, panStructValueFieldsOkBool,
    panStructValuesFieldsOkBool, panStructConvertState, panStructConvertValue,
    panStructConvertValues, evalPanValueExpFull, structCompileExp, lookupInfo] using hcase

#guard
  let source := evalPanValueExpFull
    rfieldCompileRuntime.structs rfieldCompileRuntime.locals
    rfieldCompileRuntime.globals rfieldCompileRuntime.memory
    rfieldCompileRuntime.baseAddress rfieldCompileRuntime.topAddress
    (BitVec.ofNat 64 8) rfieldCompileExpression (memoryAccess := none)
  let target := evalPanValueExpFull
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).structs
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).locals
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).globals
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).memory
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).baseAddress
    (panStructConvertState rfieldCompileContext rfieldCompileRuntime).topAddress
    (BitVec.ofNat 64 8)
    (structCompileExp rfieldCompileContext rfieldCompileExpression)
    (memoryAccess := none)
  panStructShapeEqBool
    (structOldExpShape rfieldCompileContext rfieldCompileExpression) .one &&
  panStructValueFieldsOkBool rfieldCompileRuntime.structs
    (.word (BitVec.ofNat 64 5)) &&
  (match source with
   | some (.word result) => result == BitVec.ofNat 64 5
   | _ => false) &&
  (match target with
   | some (.word result) => result == BitVec.ofNat 64 5
   | _ => false)

def finiteMapState : PanStructFiniteState Word64 (FfiState Unit) :=
  panStructFiniteStateFromMaps finiteMapRuntime
    [("local", .word (BitVec.ofNat 64 7))]
    [("global", .word (BitVec.ofNat 64 11))] [("E", .one)]
    [("f", ([], .skip, .one))]
    (by simp) (by simp) (by simp) (by simp)

def finiteMapStateAtClock (clock : Nat) :
    PanStructFiniteState Word64 (FfiState Unit) :=
  { finiteMapState with
    runtime := { finiteMapState.runtime with clock := clock } }

example : finiteMapState.runtime.locals "local" =
    some (.word (BitVec.ofNat 64 7)) := by
  rfl

example : finiteMapState.runtime.globals "global" =
    some (.word (BitVec.ofNat 64 11)) := by
  rfl

example : finiteMapState.runtime.exceptionShapes "E" = some .one := by
  rfl

example : finiteMapState.runtime.locals "local" =
    panPropsALookupEq "local" finiteMapState.locals := by
  exact finiteMapState.locals_lookup "local"

example : lookupInfo "f" finiteMapState.runtime.code =
    panPropsALookupEq "f" finiteMapState.runtime.code := by
  exact lookupInfo_eq_panPropsALookupEq "f" finiteMapState.runtime.code

example :
    (panStructConvertFiniteState finiteMapContext finiteMapState).locals =
      [("local", .word (BitVec.ofNat 64 7))] := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertValue]

example :
    (panStructConvertFiniteState finiteMapContext finiteMapState).globals =
      [("global", .word (BitVec.ofNat 64 11))] := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertValue]

example :
    (panStructConvertFiniteState finiteMapContext finiteMapState).exceptionShapes =
      [("E", .one)] := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, structCompileShape, structCompileShapeWF]

example :
    lookupInfo "f" (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.code =
      some ([], .skip, .one) := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertState, panStructConvertCode,
    structCompileShape, structCompileShapeWF, lookupInfo]

example :
    evalPanValueExps
        (panStructConvertState finiteMapContext finiteMapState.runtime).structs
        (panStructConvertState finiteMapContext finiteMapState.runtime).locals
        (panStructConvertState finiteMapContext finiteMapState.runtime).globals
        (panStructConvertState finiteMapContext finiteMapState.runtime).memory
        (panStructConvertState finiteMapContext finiteMapState.runtime).baseAddress
        (panStructConvertState finiteMapContext finiteMapState.runtime).topAddress
        (BitVec.ofNat 64 8)
        (structCompileExp.structCompileExps finiteMapContext
          ([.const (BitVec.ofNat 64 3), .const (BitVec.ofNat 64 5)] : List (Exp Word64))) =
      some [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 5)] := by
  have hsource : evalPanValueExps finiteMapState.runtime.structs
      finiteMapState.runtime.locals finiteMapState.runtime.globals
      finiteMapState.runtime.memory finiteMapState.runtime.baseAddress
      finiteMapState.runtime.topAddress (BitVec.ofNat 64 8)
      ([.const (BitVec.ofNat 64 3), .const (BitVec.ofNat 64 5)] : List (Exp Word64)) =
        some [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 5)] := by
    simp [evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp]
  have hpointwise : ∀ expression,
      expression ∈
        ([.const (BitVec.ofNat 64 3), .const (BitVec.ofNat 64 5)] : List (Exp Word64)) →
      ∀ value, evalPanValueExp finiteMapState.runtime.structs
        finiteMapState.runtime.locals finiteMapState.runtime.globals
        finiteMapState.runtime.memory finiteMapState.runtime.baseAddress
        finiteMapState.runtime.topAddress (BitVec.ofNat 64 8) expression = some value →
      evalPanValueExp
        (panStructConvertState finiteMapContext finiteMapState.runtime).structs
        (panStructConvertState finiteMapContext finiteMapState.runtime).locals
        (panStructConvertState finiteMapContext finiteMapState.runtime).globals
        (panStructConvertState finiteMapContext finiteMapState.runtime).memory
        (panStructConvertState finiteMapContext finiteMapState.runtime).baseAddress
        (panStructConvertState finiteMapContext finiteMapState.runtime).topAddress
        (BitVec.ofNat 64 8) (structCompileExp finiteMapContext expression) =
        some (panStructConvertValue value) := by
    intro expression hmem value heval
    simp only [List.mem_cons] at hmem
    rcases hmem with hfirst | hrest
    · subst expression
      simp [evalPanValueExp] at heval
      cases heval
      simp [evalPanValueExp, panStructConvertValue]
    · rcases hrest with hsecond | hnil
      · subst expression
        simp [evalPanValueExp] at heval
        cases heval
        simp [evalPanValueExp, panStructConvertValue]
      · simp at hnil
  simpa [panStructConvertValue] using panStructCompileExpsEvalOfPointwiseCorrect
    (context := finiteMapContext) (state := finiteMapState.runtime)
    (bytesInWord := BitVec.ofNat 64 8)
    (expressions := [.const (BitVec.ofNat 64 3), .const (BitVec.ofNat 64 5)])
    (values := [.word (BitVec.ofNat 64 3), .word (BitVec.ofNat 64 5)])
    hsource hpointwise

example :
    ((panStructConvertFiniteState finiteMapContext finiteMapState).runtime.locals
        "local",
      (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.globals
        "global",
      (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.exceptionShapes
        "E") =
      (some (.word (BitVec.ofNat 64 7)),
        some (.word (BitVec.ofNat 64 11)), some .one) := by
  simp [panStructConvertFiniteState, finiteMapState,
    panStructFiniteStateFromMaps, panStructConvertState, panStructConvertValue,
    panPropsALookupEq, structCompileShape, structCompileShapeWF]

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime (.skip : Prog Word64) =
      some ((.control (.normal finiteMapState.runtime.locals finiteMapState.runtime.globals
          finiteMapState.runtime.memory finiteMapState.runtime.ffi),
          finiteMapState.runtime.clock), finiteMapState.runtime) := by
  exact (panStructSkipFiniteMapEvaluatorSupport finiteMapContext statefulTestContext
    statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) finiteMapState).1

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8)
        (panStructConvertFiniteState finiteMapContext finiteMapState).runtime
        (structCompileProg finiteMapContext (.skip : Prog Word64)) =
      some ((.control (.normal
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.locals
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.globals
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.memory
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.ffi),
          (panStructConvertFiniteState finiteMapContext finiteMapState).runtime.clock),
        (panStructConvertFiniteState finiteMapContext finiteMapState).runtime) := by
  exact (panStructSkipFiniteMapEvaluatorSupport finiteMapContext statefulTestContext
    statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) finiteMapState).2

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8)
        (panStructConvertFiniteState finiteMapContext finiteMapState).runtime
        (structCompileProg finiteMapContext (.skip : Prog Word64)) =
      (panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime
        (.skip : Prog Word64)).map
        (fun (result, postState) =>
          (panStructConvertClockResult result,
            panStructConvertState finiteMapContext postState)) := by
  exact panStructFiniteMapSkipEvaluationProjection finiteMapContext
    statefulTestContext statefulTestPrimitive statefulTestHandler
    (BitVec.ofNat 64 8) finiteMapState

example : True := by
  have _hcase := panStructCompileCorrectSkipCase finiteMapContext statefulTestContext
      statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) finiteMapState
      (panSemEvaluateCodeStateWithPostState_skip statefulTestContext
        statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8)
        finiteMapState.runtime)
      rfl
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by simp [structInfosOk, finiteMapState, panStructFiniteStateFromMaps,
        finiteMapRuntime])
      (by
        intro name
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
      (by
        intro name
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
  trivial

example : True := by
  have _hcase := panStructCompileCorrectBreakCase finiteMapContext statefulTestContext
      statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) finiteMapState
      (panStructSourceBreakEvaluation statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime)
      rfl
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by simp [structInfosOk, finiteMapState, panStructFiniteStateFromMaps,
        finiteMapRuntime])
      (by
        intro name
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
      (by
        intro name
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
  trivial

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime (.break : Prog Word64) =
      some ((.control (.broke finiteMapState.runtime.locals finiteMapState.runtime.globals
        finiteMapState.runtime.memory finiteMapState.runtime.ffi),
        finiteMapState.runtime.clock), finiteMapState.runtime) := by
  exact panStructSourceBreakEvaluation statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (panStructConvertState finiteMapContext finiteMapState.runtime)
      (structCompileProg finiteMapContext (.break : Prog Word64)) =
      some ((.control (.broke
        (panStructConvertLocalMap finiteMapState.runtime.locals)
        (panStructConvertLocalMap finiteMapState.runtime.globals)
        finiteMapState.runtime.memory finiteMapState.runtime.ffi),
        finiteMapState.runtime.clock),
        panStructConvertState finiteMapContext finiteMapState.runtime) := by
  have hprojection := panStructBreakEvaluatorProjection finiteMapContext
    statefulTestContext statefulTestPrimitive statefulTestHandler
    (BitVec.ofNat 64 8) finiteMapState.runtime
  rw [panStructSourceBreakEvaluation statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime] at hprojection
  simpa [panStructCompileBreak_eq_break, panStructConvertClockResult,
    panStructConvertClockOutcome, panStructConvertControlResult] using hprojection

example : True := by
  have _hcase := panStructCompileCorrectContinueCase finiteMapContext statefulTestContext
      statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) finiteMapState
      (panStructSourceContinueEvaluation statefulTestContext statefulTestPrimitive
        statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime)
      rfl
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by simp [structInfosOk, finiteMapState, panStructFiniteStateFromMaps,
        finiteMapRuntime])
      (by
        intro name
        by_cases hname : name = "local"
        · subst name
          simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
      (by
        intro name
        by_cases hname : name = "global"
        · subst name
          simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [finiteMapContext, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
  trivial

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime
      (.continue : Prog Word64) =
      some ((.control (.continued finiteMapState.runtime.locals finiteMapState.runtime.globals
        finiteMapState.runtime.memory finiteMapState.runtime.ffi),
        finiteMapState.runtime.clock), finiteMapState.runtime) := by
  exact panStructSourceContinueEvaluation statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (panStructConvertState finiteMapContext finiteMapState.runtime)
      (structCompileProg finiteMapContext (.continue : Prog Word64)) =
      some ((.control (.continued
        (panStructConvertLocalMap finiteMapState.runtime.locals)
        (panStructConvertLocalMap finiteMapState.runtime.globals)
        finiteMapState.runtime.memory finiteMapState.runtime.ffi),
        finiteMapState.runtime.clock),
        panStructConvertState finiteMapContext finiteMapState.runtime) := by
  have hprojection := panStructContinueEvaluatorProjection finiteMapContext
    statefulTestContext statefulTestPrimitive statefulTestHandler
    (BitVec.ofNat 64 8) finiteMapState.runtime
  rw [panStructSourceContinueEvaluation statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime] at hprojection
  simpa [panStructCompileContinue_eq_continue, panStructConvertClockResult,
    panStructConvertClockOutcome, panStructConvertControlResult] using hprojection

private theorem finiteMapTickCaseRegression (clock : Nat) : True := by
  let state := finiteMapStateAtClock clock
  have _hcase := panStructCompileCorrectTickCase finiteMapContext statefulTestContext
      statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8) state
      (by rfl)
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panStructValueFieldsOkBool]
        · simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "local"
        · subst name
          simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by
        intro name value hvalue
        by_cases hname : name = "global"
        · subst name
          simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          subst value
          simp [panIsWfShapeValueBool]
        · simp [state, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime,
            panPropsALookupEq] at hvalue
          exact (hname hvalue.1.symm).elim)
      (by simp [structInfosOk, state, finiteMapStateAtClock, finiteMapState,
        panStructFiniteStateFromMaps, finiteMapRuntime])
      (by
        intro name
        by_cases hname : name = "local"
        · subst name
          simp [state, finiteMapContext, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [state, finiteMapContext, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
      (by
        intro name
        by_cases hname : name = "global"
        · subst name
          simp [state, finiteMapContext, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf]
        · simp [state, finiteMapContext, finiteMapStateAtClock, finiteMapState,
            panStructFiniteStateFromMaps, finiteMapRuntime, lookupInfo,
            panPropsALookupEq, panSemShapeOf])
  trivial

example : True := finiteMapTickCaseRegression 0

example : True := finiteMapTickCaseRegression 3

/-! These four result/state assertions pair the checked-in HOL `TimeOut` and
`NONE` rows with the concrete production evaluator representation. At clock
zero both source and converted states time out and clear locals. At clock three
both continue with normal control and decrement to clock two, preserving
locals, globals, memory, and FFI state. -/

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8) finiteMapState.runtime (.tick : Prog Word64) =
      some ((.control (.normal finiteMapState.runtime.locals finiteMapState.runtime.globals
        finiteMapState.runtime.memory finiteMapState.runtime.ffi), 2),
        { finiteMapState.runtime with clock := 2 }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, finiteMapState,
    panStructFiniteStateFromMaps, finiteMapRuntime]

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (panStructConvertFiniteState finiteMapContext
        (finiteMapStateAtClock 3)).runtime
      (structCompileProg finiteMapContext (.tick : Prog Word64)) =
      some ((.control (.normal
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.locals
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.globals
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.memory
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 3)).runtime.ffi), 2),
        { (panStructConvertFiniteState finiteMapContext
            (finiteMapStateAtClock 3)).runtime with clock := 2 }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, panStructCompileTick_eq_tick,
    finiteMapStateAtClock, finiteMapState, panStructFiniteStateFromMaps,
    finiteMapRuntime, panStructConvertFiniteState, panStructConvertState,
    panStructConvertCode, structCompileShape,
    structCompileShapeWF]

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (finiteMapStateAtClock 0).runtime (.tick : Prog Word64) =
      some ((.timeout (fun _ => none) (finiteMapStateAtClock 0).runtime.globals
        (finiteMapStateAtClock 0).runtime.memory (finiteMapStateAtClock 0).runtime.ffi, 0),
        { (finiteMapStateAtClock 0).runtime with locals := fun _ => none }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, finiteMapStateAtClock,
    finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime]

example :
    panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
      statefulTestHandler (BitVec.ofNat 64 8)
      (panStructConvertFiniteState finiteMapContext
        (finiteMapStateAtClock 0)).runtime
      (structCompileProg finiteMapContext (.tick : Prog Word64)) =
      some ((.timeout (fun _ => none)
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 0)).runtime.globals
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 0)).runtime.memory
        (panStructConvertFiniteState finiteMapContext
          (finiteMapStateAtClock 0)).runtime.ffi, 0),
        { (panStructConvertFiniteState finiteMapContext
            (finiteMapStateAtClock 0)).runtime with locals := fun _ => none }) := by
  simp [panSemEvaluateCodeStateWithPostState_tick, panStructCompileTick_eq_tick,
    finiteMapStateAtClock, finiteMapState, panStructFiniteStateFromMaps,
    finiteMapRuntime, panStructConvertFiniteState, panStructConvertState,
    panStructConvertCode, structCompileShape,
    structCompileShapeWF]

private theorem finiteMapLocalValueFieldsOk :
    panStructEveryValueFieldsOkBool finiteMapState.runtime.structs
      finiteMapState.runtime.locals := by
  intro name value hlookup
  simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
    panPropsALookupEq] at hlookup
  rcases hlookup with ⟨rfl, rfl⟩
  simp [panStructValueFieldsOkBool, finiteMapState,
    panStructFiniteStateFromMaps, finiteMapRuntime]

private theorem finiteMapGlobalValueFieldsOk :
    panStructEveryValueFieldsOkBool finiteMapState.runtime.structs
      finiteMapState.runtime.globals := by
  intro name value hlookup
  simp [finiteMapState, panStructFiniteStateFromMaps, finiteMapRuntime,
    panPropsALookupEq] at hlookup
  rcases hlookup with ⟨rfl, rfl⟩
  simp [panStructValueFieldsOkBool, finiteMapState,
    panStructFiniteStateFromMaps, finiteMapRuntime]

private theorem finiteMapLocalShapeMap :
    panStructShapeMapEq finiteMapContext.locals finiteMapState.runtime.locals := by
  intro name
  by_cases hname : name = "local"
  · subst name
    simp [finiteMapContext, finiteMapState, panStructFiniteStateFromMaps,
      finiteMapRuntime, panPropsALookupEq, lookupInfo, panSemShapeOf]
  · have hne : "local" ≠ name := Ne.symm hname
    simp [finiteMapContext, finiteMapState, panStructFiniteStateFromMaps,
      finiteMapRuntime, panPropsALookupEq, lookupInfo, hne]

private theorem finiteMapGlobalShapeMap :
    panStructShapeMapEq finiteMapContext.globals finiteMapState.runtime.globals := by
  intro name
  by_cases hname : name = "global"
  · subst name
    simp [finiteMapContext, finiteMapState, panStructFiniteStateFromMaps,
      finiteMapRuntime, panPropsALookupEq, lookupInfo, panSemShapeOf]
  · have hne : "global" ≠ name := Ne.symm hname
    simp [finiteMapContext, finiteMapState, panStructFiniteStateFromMaps,
      finiteMapRuntime, panPropsALookupEq, lookupInfo, hne]

example :
    structOldExpShape finiteMapContext (.var .local "local" : Exp Word64) = .one ∧
    panStructValueFieldsOkBool finiteMapState.runtime.structs
      (.word (BitVec.ofNat 64 7)) = true ∧
    evalPanValueExpFull
      (panStructConvertState finiteMapContext finiteMapState.runtime).structs
      (panStructConvertState finiteMapContext finiteMapState.runtime).locals
      (panStructConvertState finiteMapContext finiteMapState.runtime).globals
      (panStructConvertState finiteMapContext finiteMapState.runtime).memory
      (panStructConvertState finiteMapContext finiteMapState.runtime).baseAddress
      (panStructConvertState finiteMapContext finiteMapState.runtime).topAddress
      (BitVec.ofNat 64 8) (structCompileExp finiteMapContext
        (.var .local "local" : Exp Word64))
      (memoryAccess := none) = some (.word (BitVec.ofNat 64 7)) := by
  have hresult := panStructCompileExpCorrectVarCase finiteMapContext finiteMapState.runtime
    (BitVec.ofNat 64 8) none "local" .local (.word (BitVec.ofNat 64 7))
    (by simp [evalPanValueExpFull, finiteMapState, panStructFiniteStateFromMaps,
      finiteMapRuntime, panPropsALookupEq]) rfl finiteMapLocalValueFieldsOk finiteMapGlobalValueFieldsOk
    (by simp [structInfosOk, finiteMapState, panStructFiniteStateFromMaps,
      finiteMapRuntime]) finiteMapLocalShapeMap finiteMapGlobalShapeMap
  simpa [panSemShapeOf, panStructConvertValue] using hresult

example :
    structOldExpShape finiteMapContext (.var .global "global" : Exp Word64) = .one ∧
    panStructValueFieldsOkBool finiteMapState.runtime.structs
      (.word (BitVec.ofNat 64 11)) = true ∧
    evalPanValueExpFull
      (panStructConvertState finiteMapContext finiteMapState.runtime).structs
      (panStructConvertState finiteMapContext finiteMapState.runtime).locals
      (panStructConvertState finiteMapContext finiteMapState.runtime).globals
      (panStructConvertState finiteMapContext finiteMapState.runtime).memory
      (panStructConvertState finiteMapContext finiteMapState.runtime).baseAddress
      (panStructConvertState finiteMapContext finiteMapState.runtime).topAddress
      (BitVec.ofNat 64 8) (structCompileExp finiteMapContext
        (.var .global "global" : Exp Word64))
      (memoryAccess := none) = some (.word (BitVec.ofNat 64 11)) := by
  have hresult := panStructCompileExpCorrectVarCase finiteMapContext finiteMapState.runtime
    (BitVec.ofNat 64 8) none "global" .global (.word (BitVec.ofNat 64 11))
    (by simp [evalPanValueExpFull, finiteMapState, panStructFiniteStateFromMaps,
      finiteMapRuntime, panPropsALookupEq]) rfl finiteMapLocalValueFieldsOk finiteMapGlobalValueFieldsOk
    (by simp [structInfosOk, finiteMapState, panStructFiniteStateFromMaps,
      finiteMapRuntime]) finiteMapLocalShapeMap finiteMapGlobalShapeMap
  simpa [panSemShapeOf, panStructConvertValue] using hresult

example :
    structOldExpShape finiteMapContext (.const (BitVec.ofNat 64 13) : Exp Word64) = .one ∧
    panStructValueFieldsOkBool finiteMapState.runtime.structs
      (.word (BitVec.ofNat 64 13)) = true ∧
    evalPanValueExpFull
      (panStructConvertState finiteMapContext finiteMapState.runtime).structs
      (panStructConvertState finiteMapContext finiteMapState.runtime).locals
      (panStructConvertState finiteMapContext finiteMapState.runtime).globals
      (panStructConvertState finiteMapContext finiteMapState.runtime).memory
      (panStructConvertState finiteMapContext finiteMapState.runtime).baseAddress
      (panStructConvertState finiteMapContext finiteMapState.runtime).topAddress
      (BitVec.ofNat 64 8) (structCompileExp finiteMapContext
        (.const (BitVec.ofNat 64 13) : Exp Word64))
      (memoryAccess := none) = some (.word (BitVec.ofNat 64 13)) := by
  have hresult := panStructCompileExpCorrectConstCase finiteMapContext finiteMapState.runtime
    (BitVec.ofNat 64 8) none (BitVec.ofNat 64 13) (.word (BitVec.ofNat 64 13))
    (by simp [evalPanValueExpFull]) rfl finiteMapLocalValueFieldsOk
    finiteMapGlobalValueFieldsOk
    (by simp [structInfosOk, finiteMapState, panStructFiniteStateFromMaps,
      finiteMapRuntime]) finiteMapLocalShapeMap finiteMapGlobalShapeMap
  simpa [panSemShapeOf, panStructConvertValue] using hresult

def opCompileCaseArguments : List (Exp Word64) :=
  [.const (BitVec.ofNat 64 3), .const (BitVec.ofNat 64 5)]

def opCompileCaseValue : PanValue Word64 := .word (BitVec.ofNat 64 8)

example :
    structOldExpShape emptyStructCompileContext
        (.op .add opCompileCaseArguments : Exp Word64) = .one ∧
    panStructValueFieldsOkBool finiteMapRuntime.structs opCompileCaseValue = true ∧
    evalPanValueExp
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
      (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
      (BitVec.ofNat 64 8)
      (structCompileExp emptyStructCompileContext (.op .add opCompileCaseArguments)) =
        some (.word (BitVec.ofNat 64 8)) := by
  have hsource : evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
    finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
      finiteMapRuntime.topAddress (BitVec.ofNat 64 8)
      (.op .add opCompileCaseArguments) = some opCompileCaseValue := by
    simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, opCompileCaseArguments,
      opCompileCaseValue, finiteMapRuntime, evalPanBinOp]
  have hstructs : panStructContextShapeView emptyStructCompileContext.structs =
      panStructContextShapeView finiteMapRuntime.structs := rfl
  have hlocalsFields : panStructEveryValueFieldsOkBool finiteMapRuntime.structs
      finiteMapRuntime.locals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hglobalsFields : panStructEveryValueFieldsOkBool finiteMapRuntime.structs
      finiteMapRuntime.globals := by
    intro name value hvalue
    simp [finiteMapRuntime] at hvalue
  have hstructInfos : structInfosOk finiteMapRuntime.structs := by
    simp [structInfosOk, finiteMapRuntime]
  have hlocalsMap : panStructShapeMapEq emptyStructCompileContext.locals
      finiteMapRuntime.locals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have hglobalsMap : panStructShapeMapEq emptyStructCompileContext.globals
      finiteMapRuntime.globals := by
    intro name
    simp [emptyStructCompileContext, finiteMapRuntime, lookupInfo]
  have hconstant : ∀ word subvalue,
      evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
        finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
        finiteMapRuntime.topAddress (BitVec.ofNat 64 8) (.const word) = some subvalue →
      structOldExpShape emptyStructCompileContext (.const word) = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs subvalue = true ∧
      evalPanValueExp
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
        (BitVec.ofNat 64 8) (structCompileExp emptyStructCompileContext (.const word)) =
        some (panStructConvertValue subvalue) := by
    intro word subvalue hsub
    cases subvalue with
    | word value =>
        have heq : word = value := by simpa [evalPanValueExp] using hsub
        subst value
        simp [structOldExpShape, panSemShapeOf, panStructValueFieldsOkBool,
          evalPanValueExp, panStructConvertState,
          panStructConvertValue, emptyStructCompileContext, finiteMapRuntime]
    | rStruct values => simp [evalPanValueExp] at hsub
    | nStruct name fields => simp [evalPanValueExp] at hsub
  have hinduction : ∀ argument, argument ∈ opCompileCaseArguments → ∀ subvalue,
      evalPanValueExp finiteMapRuntime.structs finiteMapRuntime.locals
        finiteMapRuntime.globals finiteMapRuntime.memory finiteMapRuntime.baseAddress
        finiteMapRuntime.topAddress (BitVec.ofNat 64 8) argument = some subvalue →
      panStructContextShapeView emptyStructCompileContext.structs =
        panStructContextShapeView finiteMapRuntime.structs →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.locals →
      panStructEveryValueFieldsOkBool finiteMapRuntime.structs finiteMapRuntime.globals →
      structInfosOk finiteMapRuntime.structs →
      panStructShapeMapEq emptyStructCompileContext.locals finiteMapRuntime.locals →
      panStructShapeMapEq emptyStructCompileContext.globals finiteMapRuntime.globals →
      structOldExpShape emptyStructCompileContext argument = panSemShapeOf subvalue ∧
      panStructValueFieldsOkBool finiteMapRuntime.structs subvalue = true ∧
      evalPanValueExp
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).structs
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).locals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).globals
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).memory
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).baseAddress
        (panStructConvertState emptyStructCompileContext finiteMapRuntime).topAddress
        (BitVec.ofNat 64 8) (structCompileExp emptyStructCompileContext argument) =
        some (panStructConvertValue subvalue) := by
    intro argument hmem subvalue hsub _hstructs _hlocalsFields _hglobalsFields
      _hstructInfos _hlocalsMap _hglobalsMap
    simp [opCompileCaseArguments] at hmem
    rcases hmem with hmem | hmem
    · subst argument
      exact hconstant _ subvalue hsub
    · subst argument
      exact hconstant _ subvalue hsub
  have hcase := panStructCompileExpCorrectOpCase emptyStructCompileContext
    finiteMapRuntime (BitVec.ofNat 64 8) .add opCompileCaseArguments
    opCompileCaseValue hsource hstructs hlocalsFields hglobalsFields hstructInfos
    hlocalsMap hglobalsMap hinduction
  simpa [opCompileCaseArguments, opCompileCaseValue, emptyStructCompileContext,
    finiteMapRuntime, panSemShapeOf, panStructValueFieldsOkBool,
    panStructConvertValue, structCompileExp] using hcase

end Flapjack.Test
