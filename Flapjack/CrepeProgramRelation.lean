import Flapjack.CrepeDeclarationRelation

/-!
The compositional source-to-Crep program relation.

The CakeML proof is an induction over the source program evaluator.  This
module introduces the corresponding Lean predicate and proves its sequence
constructor.  The remaining constructor cases can be supplied by the
relation-aware statement lemmas without repeating evaluator inversion.
-/

namespace Flapjack

def PanValueCrepProgramCorrect
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α) : Prop :=
  ∀ (context : CompileContext α) (structs : StructContext)
    (sourceFunctions : List (FunName × List VarName × Prog α))
    (functions : List (CompiledFunction α))
    (sourceLocals sourceGlobals : VarName → Option (PanValue α))
    (sourceMemory : α → Option (PanValue α)) (state : CrepState α)
    (primitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueFfiHandler α)
    (crepPrimitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α) (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress bytesInWord : α)
    (sourceFuel targetFuel : Nat)
    (exceptionRel : ExceptionId → PanValue α → α → Prop)
    (sourceResult : PanValueControlResult α)
    (crepResult : CrepControlResult α),
    panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory state →
    evalPanValueProgWithPrimitiveCallsAndFfi
      primitive sourceHandler structs sourceFunctions
      baseAddress topAddress bytesInWord sourceFuel
      sourceLocals sourceGlobals sourceMemory program = some sourceResult →
    evalCrepFullProg functions crepPrimitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (compileProg context program) = some crepResult →
      panValueCrepControlRel structs context exceptionRel sourceResult crepResult

/-! Leaf cases for the program induction.  These are deliberately stated at
the relation boundary rather than as concrete examples: the source and Crep
evaluators must agree for every related environment and every successful fuel
bound. -/

theorem panValueCrepProgramCorrect_skip
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramCorrect (.skip : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProg] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProg] at hsource hcrep
          cases hsource
          cases hcrep
          simpa [panValueCrepControlRel] using hrel

theorem panValueCrepProgramCorrect_tick
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramCorrect (.tick : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProg] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProg] at hsource hcrep
          cases hsource
          cases hcrep
          simpa [panValueCrepControlRel] using hrel

theorem panValueCrepProgramCorrect_annot
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (tag text : String) :
    PanValueCrepProgramCorrect (.annot tag text : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProg] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProg] at hsource hcrep
          cases hsource
          cases hcrep
          simpa [panValueCrepControlRel] using hrel

theorem panValueCrepProgramCorrect_break
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramCorrect (.break : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProg] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProg] at hsource hcrep
          cases hsource
          cases hcrep
          simpa [panValueCrepControlRel] using hrel

theorem panValueCrepProgramCorrect_continue
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    PanValueCrepProgramCorrect (.continue : Prog α) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  cases sourceFuel with
  | zero => simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero => simp [evalCrepFullProg] at hcrep
      | succ targetFuel =>
          simp [evalPanValueProgWithPrimitiveCallsAndFfi, compileProg,
            evalCrepFullProg] at hsource hcrep
          cases hsource
          cases hcrep
          simpa [panValueCrepControlRel] using hrel

theorem panValueCrepProgramCorrect_seq
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (first second : Prog α)
    (hfirst : PanValueCrepProgramCorrect first)
    (hsecond : PanValueCrepProgramCorrect second) :
    PanValueCrepProgramCorrect (.seq first second) := by
  intro context structs sourceFunctions functions sourceLocals sourceGlobals
    sourceMemory state primitive sourceHandler crepPrimitive ffi sharedMem
    baseAddress topAddress bytesInWord sourceFuel targetFuel exceptionRel
    sourceResult crepResult hrel hsource hcrep
  have hcompile :
      compileProg context (.seq first second) =
        .seq (compileProg context first) (compileProg context second) := by
    simp [compileProg]
  rw [hcompile] at hcrep
  cases sourceFuel with
  | zero =>
      simp [evalPanValueProgWithPrimitiveCallsAndFfi] at hsource
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          simp [evalCrepFullProg] at hcrep
      | succ targetFuel =>
          cases hfirstSource : evalPanValueProgWithPrimitiveCallsAndFfi
              primitive sourceHandler structs sourceFunctions
              baseAddress topAddress bytesInWord sourceFuel
              sourceLocals sourceGlobals sourceMemory first with
          | none =>
              simp [evalPanValueProgWithPrimitiveCallsAndFfi,
                hfirstSource] at hsource
          | some firstSourceResult =>
              cases hfirstCrep : evalCrepFullProg functions crepPrimitive ffi sharedMem
                  baseAddress topAddress targetFuel state (compileProg context first) with
              | none =>
                  simp [evalCrepFullProg, hfirstCrep] at hcrep
              | some firstCrepResult =>
                  have hfirstRel := hfirst context structs sourceFunctions functions
                    sourceLocals sourceGlobals sourceMemory state primitive sourceHandler
                    crepPrimitive ffi sharedMem baseAddress topAddress bytesInWord
                    sourceFuel targetFuel exceptionRel firstSourceResult firstCrepResult
                    hrel hfirstSource hfirstCrep
                  cases firstSourceResult with
                  | normal firstLocals firstGlobals firstMemory =>
                      cases firstCrepResult with
                      | normal firstState =>
                          have hstateRel :
                              panValueCrepStateRel structs context firstLocals firstGlobals
                                firstMemory firstState := by
                            simpa [panValueCrepControlRel] using hfirstRel
                          have hsourceSecond :
                              evalPanValueProgWithPrimitiveCallsAndFfi
                                primitive sourceHandler structs sourceFunctions
                                baseAddress topAddress bytesInWord sourceFuel
                                firstLocals firstGlobals firstMemory second =
                              some sourceResult := by
                            simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                              hfirstSource] using hsource
                          have hcrepSecond :
                              evalCrepFullProg functions crepPrimitive ffi sharedMem
                                baseAddress topAddress targetFuel firstState
                                (compileProg context second) = some crepResult := by
                            simpa [evalCrepFullProg, hfirstCrep] using hcrep
                          exact hsecond context structs sourceFunctions functions
                            firstLocals firstGlobals firstMemory firstState primitive
                            sourceHandler crepPrimitive ffi sharedMem baseAddress topAddress
                            bytesInWord sourceFuel targetFuel exceptionRel sourceResult
                            crepResult hstateRel hsourceSecond hcrepSecond
                      | returned firstState values
                      | raised firstState exception
                      | broke firstState label
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                  | returned firstLocals firstGlobals firstMemory values =>
                      have hsourceEq :
                          PanValueControlResult.returned firstLocals firstGlobals
                              firstMemory values = sourceResult := by
                        simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                          hfirstSource] using hsource
                      cases firstCrepResult with
                      | normal firstState =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | returned firstState firstValues =>
                          have hcrepEq :
                              CrepControlResult.returned firstState firstValues =
                                crepResult := by
                            simpa [evalCrepFullProg, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstRel
                      | raised firstState exception
                      | broke firstState label
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                  | raised firstLocals firstGlobals firstMemory exception value =>
                      have hsourceEq :
                          PanValueControlResult.raised firstLocals firstGlobals
                              firstMemory exception value = sourceResult := by
                        simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                          hfirstSource] using hsource
                      cases firstCrepResult with
                      | normal firstState =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | raised firstState exceptionCode =>
                          have hcrepEq :
                              CrepControlResult.raised firstState exceptionCode =
                                crepResult := by
                            simpa [evalCrepFullProg, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstRel
                      | returned firstState values
                      | broke firstState label
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                  | broke firstLocals firstGlobals firstMemory =>
                      have hsourceEq :
                          PanValueControlResult.broke firstLocals firstGlobals
                              firstMemory = sourceResult := by
                        simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                          hfirstSource] using hsource
                      cases firstCrepResult with
                      | normal firstState =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | broke firstState label =>
                          have hcrepEq :
                              CrepControlResult.broke firstState label =
                                crepResult := by
                            simpa [evalCrepFullProg, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstRel
                      | returned firstState values
                      | raised firstState exception
                      | continued firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel
                  | continued firstLocals firstGlobals firstMemory =>
                      have hsourceEq :
                          PanValueControlResult.continued firstLocals firstGlobals
                              firstMemory = sourceResult := by
                        simpa [evalPanValueProgWithPrimitiveCallsAndFfi,
                          hfirstSource] using hsource
                      cases firstCrepResult with
                      | normal firstState =>
                          simp [panValueCrepControlRel] at hfirstRel
                      | continued firstState label =>
                          have hcrepEq :
                              CrepControlResult.continued firstState label =
                                crepResult := by
                            simpa [evalCrepFullProg, hfirstCrep] using hcrep
                          cases hsourceEq
                          cases hcrepEq
                          exact hfirstRel
                      | returned firstState values
                      | raised firstState exception
                      | broke firstState label
                      | finalFfi firstState event =>
                          simp [panValueCrepControlRel] at hfirstRel

end Flapjack
