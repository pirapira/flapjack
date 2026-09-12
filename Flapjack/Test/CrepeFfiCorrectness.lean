import Flapjack.CrepeFfiCorrectness
import Flapjack.Test.SourceToCrepeFfi

/-! A concrete regression for the reusable source-to-Crepe FFI boundary. -/

namespace Flapjack

def sourceToCrepeFfiSourceAfter : VarName → Option (RiscV.Word 64) :=
  updatePanLocal sourceToCrepeFfiSourceLocals "result"
    (BitVec.ofNat 64 41 + 1)

def sourceToCrepeFfiTargetAfterTemps : CrepState (RiscV.Word 64) :=
  { sourceToCrepeFfiState with
    locals :=
      updateCrepLocal
        (updateCrepLocal
          (updateCrepLocal
            (updateCrepLocal sourceToCrepeFfiState.locals 2
              (BitVec.ofNat 64 41))
            3 (BitVec.ofNat 64 0))
          4 (BitVec.ofNat 64 0))
        5 (BitVec.ofNat 64 0) }

def sourceToCrepeFfiTargetAfter : CrepState (RiscV.Word 64) :=
  { sourceToCrepeFfiTargetAfterTemps with
    locals := updateCrepLocal sourceToCrepeFfiTargetAfterTemps.locals 1
      (BitVec.ofNat 64 41 + 1) }

theorem sourceToCrepeFfi_simulation_theorem :
    evalCrepFullProg [] sourceToCrepeFfiPrimitive sourceToCrepeFfiHandler
      sourceToCrepeFfiSharedMem 0 100 30 sourceToCrepeFfiState
      (compileProg sourceToCrepeFfiContext sourceToCrepeFfiProgram) =
        some (.normal (restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
          sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar)) ∧
      evalPanFfiProg sourceToCrepeFfiSourceHandler
        sourceToCrepeFfiSourceLocals sourceToCrepeFfiProgram =
        some sourceToCrepeFfiSourceAfter := by
  have h := compile_full_extCall_simulation
    (context := sourceToCrepeFfiContext)
    (functions := [])
    (sourceLocals := sourceToCrepeFfiSourceLocals)
    (sourceLocals' := sourceToCrepeFfiSourceAfter)
    (state := sourceToCrepeFfiState)
    (state' := sourceToCrepeFfiTargetAfter)
    (primitive := sourceToCrepeFfiPrimitive)
    (ffi := sourceToCrepeFfiHandler)
    (sharedMem := sourceToCrepeFfiSharedMem)
    (sourceHandler := sourceToCrepeFfiSourceHandler)
    (baseAddress := 0) (topAddress := 100) (fuel := 25)
    (function := "inc")
    (configuration := .const (BitVec.ofNat 64 41))
    (configurationLength := .const (BitVec.ofNat 64 0))
    (array := .const (BitVec.ofNat 64 0))
    (arrayLength := .const (BitVec.ofNat 64 0))
    (configuration' := .const (BitVec.ofNat 64 41))
    (configurationLength' := .const (BitVec.ofNat 64 0))
    (array' := .const (BitVec.ofNat 64 0))
    (arrayLength' := .const (BitVec.ofNat 64 0))
    (configurationValue := BitVec.ofNat 64 41)
    (configurationLengthValue := BitVec.ofNat 64 0)
    (arrayValue := BitVec.ofNat 64 0)
    (arrayLengthValue := BitVec.ofNat 64 0)
    (hconfiguration := by simp [sourceToCrepeFfiContext, firstCompiledExp,
      compileExp])
    (hconfigurationLength := by simp [sourceToCrepeFfiContext, firstCompiledExp,
      compileExp])
    (harray := by simp [sourceToCrepeFfiContext, firstCompiledExp, compileExp])
    (harrayLength := by simp [sourceToCrepeFfiContext, firstCompiledExp,
      compileExp])
    (hconfigurationValue := by simp [sourceToCrepeFfiState, evalCrepFullExp])
    (hconfigurationLengthValue := by
      simp [sourceToCrepeFfiState, evalCrepFullExp])
    (harrayValue := by simp [sourceToCrepeFfiState, evalCrepFullExp])
    (harrayLengthValue := by
      simp [sourceToCrepeFfiState, evalCrepFullExp])
    (hsource := by
      simp [sourceToCrepeFfiSourceAfter, sourceToCrepeFfiSourceHandler,
        evalPanExtCall, evalPanExp])
    (hffi := by
      simp [sourceToCrepeFfiHandler, sourceToCrepeFfiState,
        sourceToCrepeFfiContext, sourceToCrepeFfiTargetAfterTemps,
        sourceToCrepeFfiTargetAfter])
  have hprogram : sourceToCrepeFfiProgram =
      (.extCall "inc" (.const (BitVec.ofNat 64 41))
        (.const (BitVec.ofNat 64 0)) (.const (BitVec.ofNat 64 0))
        (.const (BitVec.ofNat 64 0))) := by
    simp [sourceToCrepeFfiProgram]
  rw [hprogram]
  simpa [evalPanFfiProg] using h

def sourceToCrepeFfiContinuation : Prog (RiscV.Word 64) :=
  .return (.var .local "result")

def sourceToCrepeFfiSequence : Prog (RiscV.Word 64) :=
  .seq sourceToCrepeFfiProgram sourceToCrepeFfiContinuation

/-! The reusable sequencing contract carries the value produced by the FFI
step into a following source return.  This is the first concrete regression
that observes the post-FFI state through a continuation rather than only
checking the FFI leaf itself. -/

theorem sourceToCrepeFfi_sequence_simulation :
    evalCrepFullProg [] sourceToCrepeFfiPrimitive sourceToCrepeFfiHandler
      sourceToCrepeFfiSharedMem 0 100 31 sourceToCrepeFfiState
      (compileProg sourceToCrepeFfiContext sourceToCrepeFfiSequence) =
        some (.returned
          (restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
            sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar)
          [BitVec.ofNat 64 42]) ∧
      evalPanProgWithCallsAndFfi [] sourceToCrepeFfiSourceHandler 31
        sourceToCrepeFfiSourceLocals sourceToCrepeFfiSequence =
        some (.returned sourceToCrepeFfiSourceAfter [BitVec.ofNat 64 42]) := by
  have hfirst := sourceToCrepeFfi_simulation_theorem
  apply compile_full_seq_after_normal_simulation
    (context := sourceToCrepeFfiContext)
    (sourceLocals := sourceToCrepeFfiSourceLocals)
    (sourceLocals' := sourceToCrepeFfiSourceAfter)
    (state := sourceToCrepeFfiState)
    (state' := restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
      sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar)
    (primitive := sourceToCrepeFfiPrimitive)
    (ffi := sourceToCrepeFfiHandler)
    (sharedMem := sourceToCrepeFfiSharedMem)
    (sourceHandler := sourceToCrepeFfiSourceHandler)
    (baseAddress := 0) (topAddress := 100) (fuel := 29)
    (first := sourceToCrepeFfiProgram)
    (compiledFirst := compileProg sourceToCrepeFfiContext sourceToCrepeFfiProgram)
    (second := sourceToCrepeFfiContinuation)
    (compiledSecond := compileProg sourceToCrepeFfiContext
      sourceToCrepeFfiContinuation)
    (sourceResult := .returned sourceToCrepeFfiSourceAfter
      [BitVec.ofNat 64 42])
    (crepResult := .returned
      (restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
        sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar)
      [BitVec.ofNat 64 42])
    (hfirstCompile := rfl) (hsecondCompile := rfl)
    (hfirstCrep := hfirst.1)
    (hfirstSource := by
      have hfirst' : evalPanExtCall sourceToCrepeFfiSourceHandler
          sourceToCrepeFfiSourceLocals "inc"
          (.const (BitVec.ofNat 64 41)) (.const 0) (.const 0) (.const 0) =
          some sourceToCrepeFfiSourceAfter := by
        simpa [sourceToCrepeFfiProgram, evalPanFfiProg] using hfirst.2
      simp only [sourceToCrepeFfiProgram, evalPanProgWithCallsAndFfi]
      rw [hfirst']
      rfl
    )
    (hsecondCrep := by
      have hmax : sourceToCrepeFfiContext.maxVar = 1 := rfl
      have hcompiled :
          compileProg sourceToCrepeFfiContext sourceToCrepeFfiContinuation =
            .return [.var 1] := by
        simp [sourceToCrepeFfiContinuation, sourceToCrepeFfiContext,
          compileProg, compileExp, lookupInfo]
      have hlocal :
          (restoreCrepFfiTemps sourceToCrepeFfiTargetAfter
            sourceToCrepeFfiState sourceToCrepeFfiContext.maxVar).locals 1 =
            some (BitVec.ofNat 64 42) := by
        rw [hmax]
        simp [restoreCrepFfiTemps, sourceToCrepeFfiTargetAfter,
          sourceToCrepeFfiTargetAfterTemps, sourceToCrepeFfiState,
          updateCrepLocal, restoreCrepLocal]
      rw [hcompiled]
      simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
        hlocal, Option.bind]
    )
    (hsecondSource := by
      simp [sourceToCrepeFfiContinuation, sourceToCrepeFfiSourceAfter,
        evalPanProgWithCallsAndFfi, evalPanExp, updatePanLocal, Option.bind])

#guard
    (evalPanProgWithCallsAndFfi [] sourceToCrepeFfiSourceHandler 31
      sourceToCrepeFfiSourceLocals sourceToCrepeFfiSequence).map
        (fun result => match result with
        | .returned _ values => values
        | _ => []) = some [BitVec.ofNat 64 42]

#guard sourceToCrepeFfiSourceAfter "result" = some (BitVec.ofNat 64 42)

/-! Exception propagation regression for the reusable sequencing boundary. -/

def raisedSequenceContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [("E", 9)],
    maxVar := 0, bytesInWord := 8 }

def raisedSequenceFirst : Prog Nat :=
  .raise "E" (.const 3)

def raisedSequenceSecond : Prog Nat :=
  .return (.const 99)

def raisedSequenceState : CrepState Nat :=
  { locals := fun _ => none, memory := fun _ => none }

def raisedSequenceTargetState : CrepState Nat :=
  { raisedSequenceState with memory := updateMemory raisedSequenceState.memory 0 3 }

theorem raised_sequence_short_circuits_continuation :
    evalCrepFullProg [] (fun _ _ => none) (fun _ _ _ _ _ _ => none)
      defaultCrepSharedMemHandler 0 100 11 raisedSequenceState
      (compileProg raisedSequenceContext
        (.seq raisedSequenceFirst raisedSequenceSecond)) =
        some (.raised raisedSequenceTargetState 9) ∧
      evalPanProgWithCallsAndFfi [] (fun _ _ _ _ _ _ => none) 11
        (fun _ => none) (.seq raisedSequenceFirst raisedSequenceSecond) =
        some (.raised (fun _ => none) "E" 3) := by
  apply compile_full_seq_after_raise_simulation
    (context := raisedSequenceContext)
    (functions := []) (sourceFunctions := [])
    (sourceLocals := fun _ => none)
    (sourceLocals' := fun _ => none)
    (state := raisedSequenceState)
    (state' := raisedSequenceTargetState)
    (primitive := fun _ _ => none)
    (ffi := fun _ _ _ _ _ _ => none)
    (sharedMem := defaultCrepSharedMemHandler)
    (sourceHandler := fun _ _ _ _ _ _ => none)
    (baseAddress := 0) (topAddress := 100) (fuel := 9)
    (first := raisedSequenceFirst)
    (compiledFirst := compileProg raisedSequenceContext raisedSequenceFirst)
    (second := raisedSequenceSecond)
    (compiledSecond := compileProg raisedSequenceContext raisedSequenceSecond)
    (sourceException := "E") (sourceValue := 3) (compiledException := 9)
    (hfirstCompile := rfl) (hsecondCompile := rfl)
    (hfirstCrep := by
      have hrestore :
          restoreCrepLocal (α := Nat) (fun _ => none) 1 none =
            (fun _ => none) := by
        funext current
        simp [restoreCrepLocal]
      simp [raisedSequenceFirst, raisedSequenceContext, compileProg,
        compileExp, freshNames, nestedDecs, storeGlobals, crepNestedSeq,
        evalCrepFullProg, evalCrepFullExp, updateCrepLocal,
        restoreCrepResult, raisedSequenceState, raisedSequenceTargetState,
        lookupInfo, hrestore])
    (hfirstSource := by
      simp [raisedSequenceFirst, evalPanProgWithCallsAndFfi, evalPanExp])

end Flapjack
