import Flapjack.CrepeExpressionRelation
import Flapjack.CrepeProgramRelation

/-!
Program-level correctness for a two-word record declaration whose body breaks.
The declaration's temporary bindings are restored while the break result is
propagated through the source and Crep control boundaries.
-/

namespace Flapjack

set_option linter.unusedSimpArgs false in
theorem panValueCrepProgramCorrect_dec_two_word_record_break
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (left right : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (current : VarName) (value : PanValue α),
      sourceLocals current = some value →
      ∃ slot, lookupInfo current context.vars = some (.one, [slot]))
    (hstable : ∀ (state : CrepState α) (baseAddress topAddress : α)
      (temporary : Nat) (compiled : CrepExp α) (value updateValue : α),
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value →
      evalCrepFullExp
        (updateCrepLocal state.locals temporary updateValue) state.memory
        baseAddress topAddress compiled = some value) :
    PanValueCrepProgramCorrect
      (.dec name (.comb [.one, .one])
        (.rStruct [left.toExp, right.toExp]) .break) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hleft : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord left.toExp with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
            evalPanValueExp.evalPanValueExps, hleft] at hsource
      | some leftValue' =>
          obtain ⟨leftValue, hleftWord⟩ := evalPanValueExp_sourceWord_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context hrel.2.1
            (fun current value hvalue =>
              hlookup context sourceLocals current value hvalue)
            left leftValue' hleft
          have hleftSource :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord left.toExp =
                some (.word leftValue) := by
            rw [hleft, hleftWord]
          cases hright : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord right.toExp with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
                evalPanValueExp.evalPanValueExps, hleft, hright] at hsource
          | some rightValue' =>
              obtain ⟨rightValue, hrightWord⟩ := evalPanValueExp_sourceWord_inv
                structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord context hrel.2.1
                (fun current value hvalue =>
                  hlookup context sourceLocals current value hvalue)
                right rightValue' hright
              have hrightSource :
                  evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                    baseAddress topAddress bytesInWord right.toExp =
                    some (.word rightValue) := by
                rw [hright, hrightWord]
              have hrestoreSource :
                  restorePanValueLocal
                      (updatePanValueMap sourceLocals name
                        (.rStruct [.word leftValue, .word rightValue]))
                      name (sourceLocals name) = sourceLocals := by
                funext current
                by_cases hcurrent : current == name
                · have heq : current = name := by simpa using hcurrent
                  subst current
                  simp [restorePanValueLocal]
                · simp [restorePanValueLocal, updatePanValueMap, hcurrent]
              have hsourceExpected :
                  evalPanValueProgWithPrimitiveCallsAndFfi
                    primitive sourceHandler structs sourceFunctions
                    baseAddress topAddress bytesInWord (sourceFuel + 1)
                    sourceLocals sourceGlobals sourceMemory
                    (.dec name (.comb [.one, .one])
                      (.rStruct [left.toExp, right.toExp]) .break) =
                    some (.broke sourceLocals sourceGlobals sourceMemory) := by
                cases sourceFuel with
                | zero =>
                    simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
                | succ sourceFuel =>
                    simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                      evalPanValueExp, evalPanValueExp.evalPanValueExps,
                      hleftSource, hrightSource, panValueShape, panShapeMatches,
                      panShapeMatches.panShapeListMatches,
                      restorePanValueControlLocal, hrestoreSource,
                      updatePanValueMap]
              obtain ⟨compiledLeft, hcompileLeft, hcrepLeft⟩ :=
                compileSourceWordExp_relation context structs sourceLocals
                  sourceGlobals sourceMemory state.locals state.memory
                  baseAddress topAddress bytesInWord
                  (hbytesInWord context bytesInWord) hrel.2.1
                  (fun current value hvalue =>
                    hlookup context sourceLocals current value hvalue)
                  left leftValue hleftSource
              obtain ⟨compiledRight, hcompileRight, hcrepRight⟩ :=
                compileSourceWordExp_relation context structs sourceLocals
                  sourceGlobals sourceMemory state.locals state.memory
                  baseAddress topAddress bytesInWord
                  (hbytesInWord context bytesInWord) hrel.2.1
                  (fun current value hvalue =>
                    hlookup context sourceLocals current value hvalue)
                  right rightValue hrightSource
              have hcrepRightAfter := hstable state baseAddress topAddress
                (context.maxVar + 1) compiledRight rightValue leftValue
                hcrepRight
              have hcompile :
                  compileExp context (.rStruct [left.toExp, right.toExp]) =
                    ([compiledLeft, compiledRight], .comb [.one, .one]) := by
                simp [compileExp, compileExp.compileExpList, hcompileLeft,
                  hcompileRight]
              have hcompileProg :
                  compileProg context
                      (.dec name (.comb [.one, .one])
                        (.rStruct [left.toExp, right.toExp]) .break) =
                    nestedDecs [context.maxVar + 1, context.maxVar + 2]
                      [compiledLeft, compiledRight] (.break 0) := by
                simp [compileProg, hcompile, allocatedNames, Shape.shapeSize,
                  List.range, List.range.loop, compileExp,
                  compileExp.compileExpList, hcompileLeft, hcompileRight,
                  lookupInfo, Nat.add_assoc]
              have hrestore :
                  restoreCrepLocal
                      (restoreCrepLocal
                        (updateCrepLocal
                          (updateCrepLocal state.locals
                            (context.maxVar + 1) leftValue)
                          (context.maxVar + 2) rightValue)
                        (context.maxVar + 2)
                        (state.locals (context.maxVar + 2)))
                    (context.maxVar + 1)
                    (state.locals (context.maxVar + 1)) = state.locals := by
                funext current
                by_cases hsecond : current = context.maxVar + 2
                · simp [restoreCrepLocal, hsecond]
                · by_cases hfirst : current = context.maxVar + 1 <;>
                    simp [restoreCrepLocal, updateCrepLocal, hsecond, hfirst]
              rw [hcompileProg] at hcrep
              cases targetFuel with
              | zero =>
                  simp [nestedDecs, evalCrepFullProg] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [nestedDecs, evalCrepFullProg] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [nestedDecs, evalCrepFullProg,
                            evalCrepFullExps] at hcrep
                      | succ targetFuel =>
                          have htargetExpected :
                              evalCrepFullProg functions crepPrimitive ffi
                                  sharedMem baseAddress topAddress
                                  (targetFuel + 3) state
                                  (compileProg context
                                    (.dec name (.comb [.one, .one])
                                      (.rStruct [left.toExp, right.toExp]) .break)) =
                                some (.broke state 0) := by
                            rw [hcompileProg]
                            simp [nestedDecs, evalCrepFullProg, evalCrepFullExp,
                              evalCrepFullExps, hcrepLeft, hcrepRightAfter,
                              updateCrepLocal, restoreCrepResult, hrestore,
                              Nat.add_assoc]
                          have hsourceEq :=
                            Option.some.inj (hsourceExpected.symm.trans hsource)
                          have hcrepForRelation :
                              evalCrepFullProg functions crepPrimitive ffi
                                  sharedMem baseAddress topAddress
                                  (targetFuel + 3) state
                                  (compileProg context
                                    (.dec name (.comb [.one, .one])
                                      (.rStruct [left.toExp, right.toExp]) .break)) =
                                some crepResult := by
                            simpa [hcompileProg, Nat.add_assoc] using hcrep
                          have hcrepEq :=
                            Option.some.inj
                              (htargetExpected.symm.trans hcrepForRelation)
                          have hcontrol :
                              panValueCrepControlRel structs context exceptionRel
                                (.broke sourceLocals sourceGlobals sourceMemory)
                                (.broke state 0) := by
                            simpa [panValueCrepControlRel] using hrel
                          rw [hsourceEq, hcrepEq] at hcontrol
                          exact hcontrol


theorem panValueCrepProgramStateCorrect_dec_two_word_record_break
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : VarName) (left right : SourceWordExp α)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (current : VarName) (value : PanValue α),
      sourceLocals current = some value →
      ∃ slot, lookupInfo current context.vars = some (.one, [slot]))
    (hstable : ∀ (state : CrepState α) (baseAddress topAddress : α)
      (temporary : Nat) (compiled : CrepExp α) (value updateValue : α),
      evalCrepFullExpState state baseAddress topAddress compiled =
        some value →
      evalCrepFullExpState
        { state with locals := updateCrepLocal state.locals temporary updateValue }
        baseAddress topAddress compiled = some value) :
    PanValueCrepProgramStateCorrect
      (.dec name (.comb [.one, .one])
        (.rStruct [left.toExp, right.toExp]) .break) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases hleft : evalPanValueExp structs sourceLocals sourceGlobals
          sourceMemory baseAddress topAddress bytesInWord left.toExp with
      | none =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
            evalPanValueExp.evalPanValueExps, hleft] at hsource
      | some leftValue' =>
          obtain ⟨leftValue, hleftWord⟩ := evalPanValueExp_sourceWord_inv
            structs sourceLocals sourceGlobals sourceMemory
            baseAddress topAddress bytesInWord context hrel.2.1
            (fun current value hvalue =>
              hlookup context sourceLocals current value hvalue)
            left leftValue' hleft
          have hleftSource :
              evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord left.toExp =
                some (.word leftValue) := by
            rw [hleft, hleftWord]
          cases hright : evalPanValueExp structs sourceLocals sourceGlobals
              sourceMemory baseAddress topAddress bytesInWord right.toExp with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi, evalPanValueExp,
                evalPanValueExp.evalPanValueExps, hleft, hright] at hsource
          | some rightValue' =>
              obtain ⟨rightValue, hrightWord⟩ := evalPanValueExp_sourceWord_inv
                structs sourceLocals sourceGlobals sourceMemory
                baseAddress topAddress bytesInWord context hrel.2.1
                (fun current value hvalue =>
                  hlookup context sourceLocals current value hvalue)
                right rightValue' hright
              have hrightSource :
                  evalPanValueExp structs sourceLocals sourceGlobals sourceMemory
                    baseAddress topAddress bytesInWord right.toExp =
                    some (.word rightValue) := by
                rw [hright, hrightWord]
              have hrestoreSource :
                  restorePanValueLocal
                      (updatePanValueMap sourceLocals name
                        (.rStruct [.word leftValue, .word rightValue]))
                      name (sourceLocals name) = sourceLocals := by
                funext current
                by_cases hcurrent : current == name
                · have heq : current = name := by simpa using hcurrent
                  subst current
                  simp [restorePanValueLocal]
                · simp [restorePanValueLocal, updatePanValueMap, hcurrent]
              have hsourceExpected :
                  evalPanValueProgWithPrimitiveCallsAndFfi
                    primitive sourceHandler structs sourceFunctions
                    baseAddress topAddress bytesInWord (sourceFuel + 1)
                    sourceLocals sourceGlobals sourceMemory
                    (.dec name (.comb [.one, .one])
                      (.rStruct [left.toExp, right.toExp]) .break) =
                    some (.broke sourceLocals sourceGlobals sourceMemory) := by
                cases sourceFuel with
                | zero =>
                    simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
                | succ sourceFuel =>
                    simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                      evalPanValueExp, evalPanValueExp.evalPanValueExps,
                      hleftSource, hrightSource, panValueShape, panShapeMatches,
                      panShapeMatches.panShapeListMatches,
                      restorePanValueControlLocal, hrestoreSource,
                      ]
              obtain ⟨compiledLeft, hcompileLeft, hcrepLeft⟩ :=
                compileSourceWordExp_state_relation context structs sourceLocals
                  sourceGlobals sourceMemory state
                  baseAddress topAddress bytesInWord
                  (hbytesInWord context bytesInWord) hrel.2.1
                  (fun current value hvalue =>
                    hlookup context sourceLocals current value hvalue)
                  left leftValue hleftSource
              obtain ⟨compiledRight, hcompileRight, hcrepRight⟩ :=
                compileSourceWordExp_state_relation context structs sourceLocals
                  sourceGlobals sourceMemory state
                  baseAddress topAddress bytesInWord
                  (hbytesInWord context bytesInWord) hrel.2.1
                  (fun current value hvalue =>
                    hlookup context sourceLocals current value hvalue)
                  right rightValue hrightSource
              have hcrepRightAfter := hstable state baseAddress topAddress
                (context.maxVar + 1) compiledRight rightValue leftValue
                hcrepRight
              have hcompile :
                  compileExp context (.rStruct [left.toExp, right.toExp]) =
                    ([compiledLeft, compiledRight], .comb [.one, .one]) := by
                simp [compileExp, compileExp.compileExpList, hcompileLeft,
                  hcompileRight]
              have hcompileProg :
                  compileProg context
                      (.dec name (.comb [.one, .one])
                        (.rStruct [left.toExp, right.toExp]) .break) =
                    nestedDecs [context.maxVar + 1, context.maxVar + 2]
                      [compiledLeft, compiledRight] (.break 0) := by
                simp [compileProg, hcompile, allocatedNames, Shape.shapeSize,
                  List.range, List.range.loop, Nat.add_assoc]
              have hrestore :
                  restoreCrepLocal
                      (restoreCrepLocal
                        (updateCrepLocal
                          (updateCrepLocal state.locals
                            (context.maxVar + 1) leftValue)
                          (context.maxVar + 2) rightValue)
                        (context.maxVar + 2)
                        (state.locals (context.maxVar + 2)))
                    (context.maxVar + 1)
                    (state.locals (context.maxVar + 1)) = state.locals := by
                funext current
                by_cases hsecond : current = context.maxVar + 2
                · simp [restoreCrepLocal, hsecond]
                · by_cases hfirst : current = context.maxVar + 1 <;>
                    simp [restoreCrepLocal, updateCrepLocal, hsecond, hfirst]
              rw [hcompileProg] at hcrep
              cases targetFuel with
              | zero =>
                  simp [nestedDecs, evalCrepFullProgState] at hcrep
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [nestedDecs, evalCrepFullProgState] at hcrep
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [nestedDecs, evalCrepFullProgState] at hcrep
                      | succ targetFuel =>
                          have htargetExpected :
                              evalCrepFullProgState functions crepPrimitive ffi
                                  sharedMem baseAddress topAddress
                                  (targetFuel + 3) state
                                  (compileProg context
                                    (.dec name (.comb [.one, .one])
                                      (.rStruct [left.toExp, right.toExp]) .break)) =
                                some (.broke state 0) := by
                            rw [hcompileProg]
                            simp [nestedDecs, evalCrepFullProgState,
                              hcrepLeft, hcrepRightAfter, updateCrepLocal,
                              restoreCrepResult, hrestore]
                          have hsourceEq :=
                            Option.some.inj (hsourceExpected.symm.trans hsource)
                          have hcrepForRelation :
                              evalCrepFullProgState functions crepPrimitive ffi
                                  sharedMem baseAddress topAddress
                                  (targetFuel + 3) state
                                  (compileProg context
                                    (.dec name (.comb [.one, .one])
                                      (.rStruct [left.toExp, right.toExp]) .break)) =
                                some crepResult := by
                            simpa [hcompileProg, Nat.add_assoc] using hcrep
                          have hcrepEq :=
                            Option.some.inj
                              (htargetExpected.symm.trans hcrepForRelation)
                          have hcontrol :
                              panValueCrepControlRel structs context exceptionRel
                                (.broke sourceLocals sourceGlobals sourceMemory)
                                (.broke state 0) := by
                            simpa [panValueCrepControlRel] using hrel
                          rw [hsourceEq, hcrepEq] at hcontrol
                          exact hcontrol


end Flapjack
