import Flapjack.CorrectnessFfi
import Flapjack.CrepeSemantics
import Flapjack.CrepeRuntime

/-!
Crepe-to-Loop correctness for the FFI boundary.

The two evaluators use different state records even though an `extCall` has
the same observable effect in both languages.  These adapters make that
correspondence explicit and keep the proof independent of the implementation
details of `loopCompileProg`.
-/

namespace Flapjack

def loopStateOfCrepState (state : CrepState α) : LoopState α :=
  { locals := state.locals
    globals := state.globals
    memory := state.memory }

/-! Runtime state adapter retaining the explicit global environment. -/
def loopStateOfCrepRuntimeState (state : CrepRuntimeState α σ) : LoopState α :=
  { locals := state.locals
    globals := state.globals
    memory := state.memory }

def crepControlGlobalAt (address : α) : CrepControlResult α → Option α
  | .normal state => state.globals address
  | .returned state _ => state.globals address
  | .raised state _ => state.globals address
  | .broke state _ => state.globals address
  | .continued state _ => state.globals address
  | .finalFfi state _ => state.globals address

theorem crepRuntimeToLoop_storeGlob_const_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ) (live : List Nat)
    (address value : α) :
    (evalCrepRuntimeResult handler primitive (fuel + 1) state
      (.storeGlob address (.const value))).map
        (fun result => result.2.globals address) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepRuntimeState state)
      (loopCompileProg context live
        (.storeGlob address (.const value)))).map
        (fun result => (loopResultState result).globals address) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
    loopStateOfCrepRuntimeState, loopCompileProg, loopCompileExp,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg,
    evalLoopExp, loopResultState, updateMemory, updateLoopGlobal]

theorem crepRuntimeToLoop_loadGlob_const_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (handler : CrepRuntimeFfiHandler α σ ε)
    (primitive : CrepPrimitiveHandler α)
    (fuel : Nat) (state : CrepRuntimeState α σ) (live : List Nat)
    (name : Nat) (address value : α)
    (hglobal : state.globals address = some value) :
    (evalCrepRuntimeResult handler primitive (fuel + 1) state
      (.assign name (.loadGlob address))).map
        (fun result => result.2.locals name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepRuntimeState state)
      (loopCompileProg context live
        (.assign name (.loadGlob address)))).map
        (fun result => (loopResultState result).locals name) := by
  simp [evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeExp,
    loopStateOfCrepRuntimeState, loopCompileProg, loopCompileExp,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg,
    evalLoopExp, loopResultState, updateCrepLocal, updateLoopLocal, hglobal]

theorem crepFullStateToLoop_storeGlob_const_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepState α) (live : List Nat)
    (address value : α) :
    (evalCrepFullProgState [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state
      (.storeGlob address (.const value))).map
        (crepControlGlobalAt address) =
    (evalLoopProgWithCallsAndFfi []
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.storeGlob address (.const value)))).map
        (fun result => (loopResultState result).globals address) := by
  simp [evalCrepFullProgState, evalCrepFullExpState,
    loopStateOfCrepState, loopCompileProg, loopCompileExp,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg,
    evalLoopExp, loopResultState, updateMemory, updateLoopGlobal,
    crepControlGlobalAt]

def crepStateOfLoopState (state : LoopState α) : CrepState α :=
  { locals := state.locals
    memory := state.memory
    globals := state.globals }

def loopFfiOfCrepFfi (ffi : CrepFfiHandler α) :
    FunName → α → α → α → α → LoopState α → Option (LoopState α) :=
  fun function configuration configurationLength array arrayLength state =>
    match ffi function configuration configurationLength array arrayLength
      (crepStateOfLoopState state) with
    | some (.returned state) => some (loopStateOfCrepState state)
    | some (.final _) | none => none

def crepControlValues : CrepControlResult α → List α
  | .returned _ values => values
  | _ => []

def crepControlException : CrepControlResult α → Option α
  | .raised _ exception => some exception
  | _ => none

def loopControlException : LoopResult α → Option α
  | .raised _ exception => some exception
  | _ => none

def crepControlLocal (name : Nat) : CrepControlResult α → Option α
  | .normal state => state.locals name
  | .returned state _ => state.locals name
  | .raised state _ => state.locals name
  | .broke state _ => state.locals name
  | .continued state _ => state.locals name
  | .finalFfi state _ => state.locals name

def loopControlLocal (name : Nat) : LoopResult α → Option α
  | .normal state => state.locals name
  | .returned state _ => state.locals name
  | .raised state _ => state.locals name
  | .broke state _ => state.locals name
  | .continued state _ => state.locals name

def crepControlMemoryAt (address : α) : CrepControlResult α → Option α
  | .normal state => state.memory address
  | .returned state _ => state.memory address
  | .raised state _ => state.memory address
  | .broke state _ => state.memory address
  | .continued state _ => state.memory address
  | .finalFfi state _ => state.memory address

def loopControlMemoryAt (address : α) : LoopResult α → Option α
  | .normal state => state.memory address
  | .returned state _ => state.memory address
  | .raised state _ => state.memory address
  | .broke state _ => state.memory address
  | .continued state _ => state.memory address

theorem crepToLoop_full_primitive_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (destinations : List Nat) (operator : PrimOp) (arguments : List Nat)
    (name : Nat) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.primitive destinations operator arguments)).map
        (crepControlLocal name) =
    (evalLoopProgWithPrimitiveCallsAndFfi primitive functions loopFfi (fuel + 1)
      (loopStateOfCrepState state)
    (loopCompileProg context live
        (.primitive destinations operator arguments))).map
        (loopControlLocal name) := by
  have hreadAux : ∀ args : List Nat,
      args.mapM state.locals = loopReadLocals state.locals args := by
    intro args
    induction args with
    | nil => rfl
    | cons argument arguments ih =>
        simp [loopReadLocals, ih]
  have hread := hreadAux arguments
  have hfold (base : Nat → Option α) (entries : List (Nat × α)) :
      List.foldl (fun locals entry =>
        updateCrepLocal locals entry.fst entry.snd) base entries =
      List.foldl (fun locals entry =>
        updateLoopLocal locals entry.fst entry.snd) base entries := by
    induction entries generalizing base with
    | nil => rfl
    | cons entry entries ih =>
        cases entry with
        | mk name value =>
            simp only [List.foldl]
            rw [show updateCrepLocal base name value =
              updateLoopLocal base name value by rfl]
            exact ih _
  cases hargs : loopReadLocals state.locals arguments with
  | none =>
      simp [evalCrepFullProg, loopCompileProg,
        evalLoopProgWithPrimitiveCallsAndFfi, assignCrepValues,
        loopAssignValues, hread, hargs, loopStateOfCrepState]
  | some values =>
      cases hprimitive : primitive operator values with
      | none =>
          simp [evalCrepFullProg, loopCompileProg,
            evalLoopProgWithPrimitiveCallsAndFfi, assignCrepValues,
            loopAssignValues, hread, hargs, hprimitive,
            loopStateOfCrepState]
      | some result =>
          by_cases hlength : destinations.length = result.length
          · simp [evalCrepFullProg, loopCompileProg,
              evalLoopProgWithPrimitiveCallsAndFfi, assignCrepValues,
              loopAssignValues, hread, hargs, hprimitive, hlength, hfold,
              loopStateOfCrepState, crepControlLocal, loopControlLocal]
          · simp [evalCrepFullProg, loopCompileProg,
              evalLoopProgWithPrimitiveCallsAndFfi, assignCrepValues,
              loopAssignValues, hread, hargs, hprimitive, hlength, hfold,
              loopStateOfCrepState]

theorem crepToLoop_seq_normal_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state middle : CrepState α) (live : List Nat)
    (first second : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hfirst : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state first = some (.normal middle))
    (hloopFirst : evalLoopProgWithCallsAndFfi loopFunctions
      loopFfi (fuel + 1) (loopStateOfCrepState state)
      (loopCompileProg context live first) =
      some (.normal (loopStateOfCrepState middle)))
    (hsecond : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) middle second = some result)
    (hloopSecond : evalLoopProgWithCallsAndFfi loopFunctions
      loopFfi (fuel + 1) (loopStateOfCrepState middle)
      (loopCompileProg context live second) = some loopResult) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state (.seq first second) = some result ∧
    evalLoopProgWithCallsAndFfi loopFunctions loopFfi
      (fuel + 2) (loopStateOfCrepState state)
      (loopCompileProg context live (.seq first second)) = some loopResult := by
  constructor
  · simp [evalCrepFullProg, hfirst, hsecond]
  · simp [loopCompileProg_seq, evalLoopProgWithCallsAndFfi,
      hloopFirst, hloopSecond]

theorem crepToLoop_seq_normal_compose_loop_extra
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state middle : CrepState α) (live : List Nat)
    (first second : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hfirst : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state first = some (.normal middle))
    (hloopFirst : evalLoopProgWithCallsAndFfi loopFunctions loopFfi
      (fuel + 2) (loopStateOfCrepState state)
      (loopCompileProg context live first) =
      some (.normal (loopStateOfCrepState middle)))
    (hsecond : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) middle second = some result)
    (hloopSecond : evalLoopProgWithCallsAndFfi loopFunctions loopFfi
      (fuel + 2) (loopStateOfCrepState middle)
      (loopCompileProg context live second) = some loopResult) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state (.seq first second) = some result ∧
    evalLoopProgWithCallsAndFfi loopFunctions loopFfi
      (fuel + 3) (loopStateOfCrepState state)
      (loopCompileProg context live (.seq first second)) =
      some loopResult := by
  constructor
  · simp [evalCrepFullProg, hfirst, hsecond]
  · simp [loopCompileProg_seq, evalLoopProgWithCallsAndFfi,
      hloopFirst, hloopSecond]

theorem crepToLoop_seq_terminal_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (first second : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hfirst : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state first = some result)
    (hloopFirst : evalLoopProgWithCallsAndFfi loopFunctions loopFfi
      (fuel + 1) (loopStateOfCrepState state)
      (loopCompileProg context live first) = some loopResult)
    (hcrepTerminal : ∀ middle : CrepState α, result ≠ .normal middle)
    (hloopTerminal : ∀ middle : LoopState α, loopResult ≠ .normal middle) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state (.seq first second) = some result ∧
    evalLoopProgWithCallsAndFfi loopFunctions loopFfi
      (fuel + 2) (loopStateOfCrepState state)
      (loopCompileProg context live (.seq first second)) = some loopResult := by
  constructor
  · simp only [evalCrepFullProg]
    rw [hfirst]
    cases result with
    | normal middle => exact (hcrepTerminal middle rfl).elim
    | returned state values => rfl
    | raised state exception => rfl
    | broke state label => rfl
    | continued state label => rfl
    | finalFfi state event => rfl
  · simp only [loopCompileProg_seq, evalLoopProgWithCallsAndFfi]
    rw [hloopFirst]
    cases loopResult with
    | normal middle => exact (hloopTerminal middle rfl).elim
    | returned state values => rfl
    | raised state exception => rfl
    | broke state label => rfl
    | continued state label => rfl

theorem crepToLoop_seq_terminal_compose_loop_extra
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α)
    (first second : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hfirst : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state first = some result)
    (hloopFirst : evalLoopProgWithCallsAndFfi loopFunctions loopFfi
      (fuel + 2) (loopStateOfCrepState state)
      (loopCompileProg context [] first) = some loopResult)
    (hcrepTerminal : ∀ middle : CrepState α, result ≠ .normal middle)
    (hloopTerminal : ∀ middle : LoopState α, loopResult ≠ .normal middle) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state (.seq first second) = some result ∧
    evalLoopProgWithCallsAndFfi loopFunctions loopFfi
      (fuel + 3) (loopStateOfCrepState state)
      (loopCompileProg context [] (.seq first second)) = some loopResult := by
  constructor
  · simp only [evalCrepFullProg]
    rw [hfirst]
    cases result with
    | normal middle => exact (hcrepTerminal middle rfl).elim
    | returned state values => rfl
    | raised state exception => rfl
    | broke state label => rfl
    | continued state label => rfl
    | finalFfi state event => rfl
  · simp only [loopCompileProg_seq, evalLoopProgWithCallsAndFfi]
    rw [hloopFirst]
    cases loopResult with
    | normal middle => exact (hloopTerminal middle rfl).elim
    | returned state values => rfl
    | raised state exception => rfl
    | broke state label => rfl
    | continued state label => rfl

theorem crepToLoop_assign_agreement_of_empty_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name : Nat) (expression : CrepExp α) (value : α)
    (hcode : (loopCompileExp context (context.maxVar + 1) live expression).code = [])
    (hvalue : evalCrepFullExp state.locals state.memory baseAddress topAddress expression =
      some value)
    (heval : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live expression).expression =
      some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.assign name expression)).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.assign name expression))).map
        (loopControlLocal name) := by
  have heval' : evalLoopExp
      ({ locals := state.locals, globals := state.globals,
         memory := state.memory } : LoopState α)
      (loopCompileExp context (context.maxVar + 1) live expression).expression =
      some value := by
    simpa [loopStateOfCrepState] using heval
  simp [evalCrepFullProg, hvalue,
    loopCompileProg, hcode, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg,
    loopStateOfCrepState, updateCrepLocal, crepControlLocal]
  rw [heval']
  simp [loopControlLocal, updateLoopLocal]

theorem crepToLoop_assign_load32_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name : Nat) (address value : α)
    (hmemory : state.memory address = some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.assign name (.load32 (.const address)))).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 5)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.assign name (.load32 (.const address))))).map
        (loopControlLocal name) := by
  simp [evalCrepFullProg, evalCrepFullExp, hmemory,
    loopCompileProg, loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopStateOfCrepState, updateCrepLocal, updateLoopLocal,
    crepControlLocal, loopControlLocal]

theorem crepToLoop_assign_loadByte_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name : Nat) (address value : α)
    (hmemory : state.memory address = some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.assign name (.loadByte (.const address)))).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 5)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.assign name (.loadByte (.const address))))).map
        (loopControlLocal name) := by
  simp [evalCrepFullProg, evalCrepFullExp, hmemory,
    loopCompileProg, loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopStateOfCrepState, updateCrepLocal, updateLoopLocal,
    crepControlLocal, loopControlLocal]

theorem crepToLoop_store_const_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (address value : α) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.store (.const address) (.const value))).map
        (crepControlMemoryAt address) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 4)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.store (.const address) (.const value)))).map
        (loopControlMemoryAt address) := by
  simp [evalCrepFullProg, evalCrepFullExp,
    crepControlMemoryAt, loopControlMemoryAt,
    loopCompileProg, loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopStateOfCrepState, updateMemory, updateLoopMemory,
    updateLoopLocal]

theorem crepToLoop_store_of_empty_prefix
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (addressExpression valueExpression : CrepExp α)
    (address value : α)
    (haddressCode :
      (loopCompileExp context (context.maxVar + 1) live addressExpression).code = [])
    (haddressNext :
      (loopCompileExp context (context.maxVar + 1) live addressExpression).nextTemp =
        context.maxVar + 1)
    (haddressLive :
      (loopCompileExp context (context.maxVar + 1) live addressExpression).live = live)
    (hvalueCode :
      (loopCompileExp context (context.maxVar + 1) live valueExpression).code = [])
    (hvalueNext :
      (loopCompileExp context (context.maxVar + 1) live valueExpression).nextTemp =
        context.maxVar + 1)
    (haddressValue : evalCrepFullExp state.locals state.memory baseAddress topAddress
      addressExpression = some address)
    (hvalueValue : evalCrepFullExp state.locals state.memory baseAddress topAddress
      valueExpression = some value)
    (hloopAddress : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live addressExpression).expression =
      some address)
    (hloopValue : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live valueExpression).expression =
      some value)
    (hloopAddressAfter :
      evalLoopExp
        ({ locals := updateLoopLocal state.locals (context.maxVar + 1) value,
           globals := state.globals, memory := state.memory } : LoopState α)
        (loopCompileExp context (context.maxVar + 1) live addressExpression).expression =
      some address) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.store addressExpression valueExpression)).map
        (crepControlMemoryAt address) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 4)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.store addressExpression valueExpression))).map
        (loopControlMemoryAt address) := by
  have hloopAddress' :
      evalLoopExp
          ({ locals := state.locals, globals := state.globals,
             memory := state.memory } : LoopState α)
          (loopCompileExp context (context.maxVar + 1) live addressExpression).expression =
        some address := by
    simpa [loopStateOfCrepState] using hloopAddress
  have hloopValue' :
      evalLoopExp
          ({ locals := state.locals, globals := state.globals,
             memory := state.memory } : LoopState α)
          (loopCompileExp context (context.maxVar + 1) live valueExpression).expression =
        some value := by
    simpa [loopStateOfCrepState] using hloopValue
  simp [evalCrepFullProg, haddressValue, hvalueValue,
    crepControlMemoryAt, loopControlMemoryAt, loopCompileProg,
    loopNestedSeq, evalLoopProgWithCallsAndFfi,
    evalLoopProg, loopStateOfCrepState, updateMemory,
    updateLoopMemory, updateLoopLocal, haddressCode, haddressNext,
    haddressLive, hvalueCode, hvalueNext, hloopValue',
    hloopAddressAfter]

theorem crepToLoop_store32_const_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (address value : α) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.store32 (.const address) (.const value))).map
        (crepControlMemoryAt address) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 5)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.store32 (.const address) (.const value)))).map
        (loopControlMemoryAt address) := by
  simp [evalCrepFullProg, evalCrepFullExp,
    crepControlMemoryAt, loopControlMemoryAt,
    loopCompileProg, loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopStateOfCrepState, updateMemory, updateLoopMemory,
    updateLoopLocal]

theorem crepToLoop_storeByte_const_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (address value : α) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.storeByte (.const address) (.const value))).map
        (crepControlMemoryAt address) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 5)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.storeByte (.const address) (.const value)))).map
        (loopControlMemoryAt address) := by
  simp [evalCrepFullProg, evalCrepFullExp,
    crepControlMemoryAt, loopControlMemoryAt,
    loopCompileProg, loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopStateOfCrepState, updateMemory, updateLoopMemory,
    updateLoopLocal]

/-!
The source shared-memory handler is an explicit effect, whereas the Loop
evaluator models the same operations through its executable memory.  These
lemmas are the boundary contract needed to connect the two presentations.
The handler hypotheses intentionally expose only the observation used by the
caller: stores need the resulting memory cell, and loads need the resulting
local.  This keeps the contract applicable to handlers that carry additional
state in their other fields.
-/

theorem crepToLoop_shMem_store_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (hoperator : operator = .store ∨ operator = .store8 ∨
      operator = .store16 ∨ operator = .store32)
    (hvalue : state.locals name = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htargetMemory : targetState.memory address = some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.shMem operator name (.const address))).map
        (crepControlMemoryAt address) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.shMem operator name (.const address)))).map
        (loopControlMemoryAt address) := by
  rcases hoperator with rfl | rfl | rfl | rfl <;>
    simp [evalCrepFullProg, evalCrepFullExp, hshared,
      crepControlMemoryAt, loopControlMemoryAt,
      loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
      loopStateOfCrepState, updateLoopMemory, hvalue,
      htargetMemory]

theorem crepToLoop_shMem_store_of_empty_prefix
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat)
    (addressExpression : CrepExp α) (address : α) (value : α)
    (hoperator : operator = .store ∨ operator = .store8 ∨
      operator = .store16 ∨ operator = .store32)
    (hcode : (loopCompileExp context (context.maxVar + 1) live
      addressExpression).code = [])
    (haddress : evalCrepFullExp state.locals state.memory baseAddress topAddress
      addressExpression = some address)
    (hloopAddress : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live addressExpression).expression =
      some address)
    (hvalue : state.locals name = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htarget : targetState =
      { state with memory := updateMemory state.memory address value }) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.shMem operator name addressExpression) =
        some (.normal targetState) ∧
    evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.shMem operator name addressExpression)) =
        some (.normal (loopStateOfCrepState targetState)) := by
  have hloopAddress' :
      evalLoopExp
          ({ locals := state.locals, globals := state.globals,
             memory := state.memory } : LoopState α)
          (loopCompileExp context (context.maxVar + 1) live addressExpression).expression =
        some address := by
    simpa [loopStateOfCrepState] using hloopAddress
  rcases hoperator with rfl | rfl | rfl | rfl
  all_goals
    subst targetState
    have hmemoryUpdate : updateLoopMemory state.memory address value =
        updateMemory state.memory address value := by
      funext current
      by_cases h : address = current
      · subst current
        simp [updateLoopMemory, updateMemory]
      · have h' : current ≠ address := Ne.symm h
        simp [updateLoopMemory, updateMemory, h, h']
    simp [evalCrepFullProg, haddress, hshared, hcode, loopCompileProg,
      loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg,
      loopStateOfCrepState, hvalue, hmemoryUpdate, hloopAddress']

theorem crepToLoop_shMem_store_state_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (hoperator : operator = .store ∨ operator = .store8 ∨
      operator = .store16 ∨ operator = .store32)
    (hvalue : state.locals name = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htarget : targetState =
      { state with memory := updateMemory state.memory address value }) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.shMem operator name (.const address)) =
        some (.normal targetState) ∧
    evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.shMem operator name (.const address))) =
        some (.normal (loopStateOfCrepState targetState)) := by
  rcases hoperator with rfl | rfl | rfl | rfl
  all_goals
    subst targetState
    have hmemoryUpdate : updateLoopMemory state.memory address value =
        updateMemory state.memory address value := by
      funext current
      by_cases h : address = current
      · subst current
        simp [updateLoopMemory, updateMemory]
      · have h' : current ≠ address := Ne.symm h
        simp [updateLoopMemory, updateMemory, h, h']
    simp [evalCrepFullProg, evalCrepFullExp, hshared,
      loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
      loopStateOfCrepState, hvalue, hmemoryUpdate]

theorem crepToLoop_shMem_store_seq_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (second : CrepProg α) (result : CrepControlResult α)
    (loopResult : LoopResult α)
    (hoperator : operator = .store ∨ operator = .store8 ∨
      operator = .store16 ∨ operator = .store32)
    (hvalue : state.locals name = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htarget : targetState =
      { state with memory := updateMemory state.memory address value })
    (hsecond : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) targetState second = some result)
    (hloopSecond : evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState targetState)
      (loopCompileProg context live second) = some loopResult) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 2) state
      (.seq (.shMem operator name (.const address)) second) = some result ∧
    evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 3)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.seq (.shMem operator name (.const address)) second)) =
      some loopResult := by
  have hfirst := crepToLoop_shMem_store_state_agreement
    context functions primitive ffi sharedMem baseAddress topAddress fuel
    state targetState live operator name address value hoperator hvalue hshared
    htarget
  exact crepToLoop_seq_normal_compose_loop_extra
    context [] functions primitive ffi
    (fun _ _ _ _ _ loopState => some loopState) sharedMem
    baseAddress topAddress fuel state targetState live
    (.shMem operator name (.const address)) second result loopResult
    hfirst.1 hfirst.2 hsecond hloopSecond

theorem crepToLoop_shMem_load_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (hoperator : operator = .load ∨ operator = .load8 ∨
      operator = .load16 ∨ operator = .load32)
    (hmemory : state.memory address = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htargetLocal : targetState.locals name = some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.shMem operator name (.const address))).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.shMem operator name (.const address)))).map
        (loopControlLocal name) := by
  rcases hoperator with rfl | rfl | rfl | rfl <;>
    simp [evalCrepFullProg, evalCrepFullExp, hmemory, hshared,
      crepControlLocal, loopControlLocal,
      loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
      loopStateOfCrepState, updateLoopLocal, htargetLocal]

theorem crepToLoop_shMem_load_of_empty_prefix
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat)
    (addressExpression : CrepExp α) (address value : α)
    (hoperator : operator = .load ∨ operator = .load8 ∨
      operator = .load16 ∨ operator = .load32)
    (hcode : (loopCompileExp context (context.maxVar + 1) live
      addressExpression).code = [])
    (haddress : evalCrepFullExp state.locals state.memory baseAddress topAddress
      addressExpression = some address)
    (hloopAddress : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live addressExpression).expression =
      some address)
    (hmemory : state.memory address = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htarget : targetState =
      { state with locals := updateCrepLocal state.locals name value }) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.shMem operator name addressExpression) =
        some (.normal targetState) ∧
    evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.shMem operator name addressExpression)) =
        some (.normal (loopStateOfCrepState targetState)) := by
  have hloopAddress' :
      evalLoopExp
          ({ locals := state.locals, globals := state.globals,
             memory := state.memory } : LoopState α)
          (loopCompileExp context (context.maxVar + 1) live addressExpression).expression =
        some address := by
    simpa [loopStateOfCrepState] using hloopAddress
  rcases hoperator with rfl | rfl | rfl | rfl
  all_goals
    subst targetState
    have hlocalUpdate : updateLoopLocal state.locals name value =
        updateCrepLocal state.locals name value := by
      rfl
    simp [evalCrepFullProg, haddress, hmemory, hshared, hcode,
      loopCompileProg, loopNestedSeq, evalLoopProgWithCallsAndFfi,
      evalLoopProg, loopStateOfCrepState, hlocalUpdate, hloopAddress']

theorem crepToLoop_shMem_load_state_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (hoperator : operator = .load ∨ operator = .load8 ∨
      operator = .load16 ∨ operator = .load32)
    (hmemory : state.memory address = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htarget : targetState =
      { state with locals := updateCrepLocal state.locals name value }) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.shMem operator name (.const address)) =
        some (.normal targetState) ∧
    evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.shMem operator name (.const address))) =
        some (.normal (loopStateOfCrepState targetState)) := by
  rcases hoperator with rfl | rfl | rfl | rfl
  all_goals
    subst targetState
    have hlocalUpdate : updateLoopLocal state.locals name value =
        updateCrepLocal state.locals name value := by
      rfl
    simp [evalCrepFullProg, evalCrepFullExp, hmemory, hshared,
      loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
      loopStateOfCrepState, hlocalUpdate]

theorem crepToLoop_shMem_load_seq_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (second : CrepProg α) (result : CrepControlResult α)
    (loopResult : LoopResult α)
    (hoperator : operator = .load ∨ operator = .load8 ∨
      operator = .load16 ∨ operator = .load32)
    (hmemory : state.memory address = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htarget : targetState =
      { state with locals := updateCrepLocal state.locals name value })
    (hsecond : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) targetState second = some result)
    (hloopSecond : evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState targetState)
      (loopCompileProg context live second) = some loopResult) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 2) state
      (.seq (.shMem operator name (.const address)) second) = some result ∧
    evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 3)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.seq (.shMem operator name (.const address)) second)) =
      some loopResult := by
  have hfirst := crepToLoop_shMem_load_state_agreement
    context functions primitive ffi sharedMem baseAddress topAddress fuel
    state targetState live operator name address value hoperator hmemory hshared
    htarget
  exact crepToLoop_seq_normal_compose_loop_extra
    context [] functions primitive ffi
    (fun _ _ _ _ _ loopState => some loopState) sharedMem
    baseAddress topAddress fuel state targetState live
    (.shMem operator name (.const address)) second result loopResult
    hfirst.1 hfirst.2 hsecond hloopSecond

theorem crepToLoop_skip_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (name : Nat) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.skip)).map (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 1)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.skip))).map (loopControlLocal name) := by
  simp [evalCrepFullProg, loopCompileProg,
    evalLoopProgWithCallsAndFfi, evalLoopProg,
    loopStateOfCrepState, crepControlLocal, loopControlLocal]

theorem crepToLoop_tick_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (name : Nat) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.tick)).map (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 1)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.tick))).map (loopControlLocal name) := by
  simp [evalCrepFullProg, loopCompileProg,
    evalLoopProgWithCallsAndFfi, evalLoopProg,
    loopStateOfCrepState, crepControlLocal, loopControlLocal]

theorem crepToLoop_break_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (label name : Nat) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.break label)).map (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 1)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.break label))).map (loopControlLocal name) := by
  simp [evalCrepFullProg, loopCompileProg,
    evalLoopProgWithCallsAndFfi, evalLoopProg,
    loopStateOfCrepState, crepControlLocal, loopControlLocal]

theorem crepToLoop_continue_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (label name : Nat) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.continue label)).map (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 1)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.continue label))).map (loopControlLocal name) := by
  simp [evalCrepFullProg, loopCompileProg,
    evalLoopProgWithCallsAndFfi, evalLoopProg,
    loopStateOfCrepState, crepControlLocal, loopControlLocal]

theorem crepToLoop_while_const_zero_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (name : Nat)
    (body : CrepProg α)
    (hname : name ≠ context.maxVar + 1) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.while (.const (by exact 0)) body)).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 12)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.while (.const (by exact 0)) body))).map
        (loopControlLocal name) := by
  simp [evalCrepFullProg, evalCrepFullExp,
    loopStateOfCrepState, crepControlLocal, loopControlLocal,
    loopCompileProg, loopCompileExp, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    evalLoopRepeatWithCallsAndFfi,
    evalLoopCondition, updateLoopLocal, hname]

theorem crepToLoop_ite_const_zero_compose
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (thenBranch elseBranch : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hcrepElse : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress fuel state elseBranch = some result)
    (hloopElse : evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      { loopStateOfCrepState state with
        locals := updateLoopLocal (loopStateOfCrepState state).locals
          (context.maxVar + 1) 0 }
      (loopCompileProg context live elseBranch) = some loopResult) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state
      (.ite (.const (by exact 0)) thenBranch elseBranch) = some result ∧
    evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 5)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.ite (.const (by exact 0)) thenBranch elseBranch)) =
      some loopResult := by
  constructor
  · simp [evalCrepFullProg, evalCrepFullExp, hcrepElse]
  · simp [loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
      evalLoopCondition, updateLoopLocal, hloopElse]

theorem crepToLoop_ite_false_of_empty_prefix
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (condition : CrepExp α) (thenBranch elseBranch : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hcode : (loopCompileExp context (context.maxVar + 1) live condition).code = [])
    (hnext : (loopCompileExp context (context.maxVar + 1) live condition).nextTemp =
      context.maxVar + 1)
    (hlive : (loopCompileExp context (context.maxVar + 1) live condition).live = live)
    (hvalue : evalCrepFullExp state.locals state.memory baseAddress topAddress
      condition = some 0)
    (hloopValue : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live condition).expression =
      some 0)
    (hcrepElse : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress fuel state elseBranch = some result)
    (hloopElse : evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      { loopStateOfCrepState state with
        locals := updateLoopLocal (loopStateOfCrepState state).locals
          (context.maxVar + 1) 0 }
      (loopCompileProg context live elseBranch) = some loopResult) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.ite condition thenBranch elseBranch) = some result ∧
    evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 5)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.ite condition thenBranch elseBranch)) =
      some loopResult := by
  have hloopValue' :
      evalLoopExp
          ({ locals := state.locals, globals := state.globals,
             memory := state.memory } : LoopState α)
          (loopCompileExp context (context.maxVar + 1) live condition).expression =
        some 0 := by
    simpa [loopStateOfCrepState] using hloopValue
  constructor
  · simp [evalCrepFullProg, hvalue, hcrepElse]
  · simp [loopCompileProg, loopNestedSeq,
      evalLoopProgWithCallsAndFfi, evalLoopProg,
      evalLoopCondition, loopStateOfCrepState, updateLoopLocal,
      hcode, hnext, hlive,
      hloopValue']
    exact hloopElse

theorem crepToLoop_ite_true_of_empty_prefix
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (condition : CrepExp α) (thenBranch elseBranch : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hcode : (loopCompileExp context (context.maxVar + 1) live condition).code = [])
    (hnext : (loopCompileExp context (context.maxVar + 1) live condition).nextTemp =
      context.maxVar + 1)
    (hlive : (loopCompileExp context (context.maxVar + 1) live condition).live = live)
    (hvalue : evalCrepFullExp state.locals state.memory baseAddress topAddress
      condition = some 1)
    (hone : (1 : α) ≠ 0)
    (hloopValue : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live condition).expression =
      some 1)
    (hcrepThen : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress fuel state thenBranch = some result)
    (hloopThen : evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      { loopStateOfCrepState state with
        locals := updateLoopLocal (loopStateOfCrepState state).locals
          (context.maxVar + 1) 1 }
      (loopCompileProg context live thenBranch) = some loopResult) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.ite condition thenBranch elseBranch) = some result ∧
    evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 5)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.ite condition thenBranch elseBranch)) =
      some loopResult := by
  have hloopValue' :
      evalLoopExp
          ({ locals := state.locals, globals := state.globals,
             memory := state.memory } : LoopState α)
          (loopCompileExp context (context.maxVar + 1) live condition).expression =
        some 1 := by
    simpa [loopStateOfCrepState] using hloopValue
  constructor
  · simp [evalCrepFullProg, hvalue, hone, hcrepThen]
  · simp [loopCompileProg, loopNestedSeq,
      evalLoopProgWithCallsAndFfi, evalLoopProg,
      evalLoopCondition, loopStateOfCrepState, updateLoopLocal,
      hcode, hnext, hlive, hone, hloopValue']
    exact hloopThen

theorem crepToLoop_while_false_of_empty_prefix
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (condition : CrepExp α) (body : CrepProg α)
    (name : Nat)
    (hname : name ≠ context.maxVar + 1)
    (hcode : (loopCompileExp context (context.maxVar + 1) live condition).code = [])
    (hnext : (loopCompileExp context (context.maxVar + 1) live condition).nextTemp =
      context.maxVar + 1)
    (hlive : (loopCompileExp context (context.maxVar + 1) live condition).live = live)
    (hvalue : evalCrepFullExp state.locals state.memory baseAddress topAddress
      condition = some 0)
    (hloopValue : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live condition).expression =
      some 0) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.while condition body)).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 12)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.while condition body))).map
        (loopControlLocal name) := by
  have hloopValue' :
      evalLoopExp
          ({ locals := state.locals, globals := state.globals,
             memory := state.memory } : LoopState α)
          (loopCompileExp context (context.maxVar + 1) live condition).expression =
        some 0 := by
    simpa [loopStateOfCrepState] using hloopValue
  simp [evalCrepFullProg, hvalue, crepControlLocal,
    loopControlLocal, loopCompileProg, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopCondition,
    evalLoopRepeatWithCallsAndFfi, loopStateOfCrepState,
    updateLoopLocal, hname, hcode, hnext, hlive, hloopValue']

theorem crepToLoop_while_true_break_of_empty_prefix
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (condition : CrepExp α) (name : Nat)
    (hname : name ≠ context.maxVar + 1)
    (hcode : (loopCompileExp context (context.maxVar + 1) live condition).code = [])
    (hnext : (loopCompileExp context (context.maxVar + 1) live condition).nextTemp =
      context.maxVar + 1)
    (hlive : (loopCompileExp context (context.maxVar + 1) live condition).live = live)
    (hvalue : evalCrepFullExp state.locals state.memory baseAddress topAddress
      condition = some 1)
    (hloopValue : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live condition).expression =
      some 1) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 2) state (.while condition (.break 0))).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 13)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.while condition (.break 0)))).map
        (loopControlLocal name) := by
  have hloopValue' :
      evalLoopExp
          ({ locals := state.locals, globals := state.globals,
             memory := state.memory } : LoopState α)
          (loopCompileExp context (context.maxVar + 1) live condition).expression =
        some 1 := by
    simpa [loopStateOfCrepState] using hloopValue
  simp [evalCrepFullProg, hvalue, crepControlLocal,
    loopControlLocal, loopCompileProg, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg,
    evalLoopCondition, evalLoopRepeatWithCallsAndFfi,
    loopStateOfCrepState, updateLoopLocal, hname, hcode, hnext, hlive,
    hloopValue']

theorem crepToLoop_return_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (value : α) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.return [.const value])).map crepControlValues =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 12)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.return [.const value]))).map loopResultValues := by
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp, crepControlValues,
    loopCompileProg,
    loopCompileExp, loopCompileExp.loopCompileExps, loopCompileExps,
    loopNestedSeq, loopTempNames, loopAssignTemps,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopReadLocals, updateLoopLocal, loopResultValues]

theorem crepToLoop_return_of_empty_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (expression : CrepExp α) (value : α)
    (hcode : (loopCompileExp context (context.maxVar + 1) live expression).code = [])
    (hvalue : evalCrepFullExp state.locals state.memory baseAddress topAddress
      expression = some value)
    (hloopValue : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live expression).expression =
      some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.return [expression])).map crepControlValues =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 12)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.return [expression]))).map
      loopResultValues := by
  have hloopValue' :
      evalLoopExp
          ({ locals := state.locals, globals := state.globals,
             memory := state.memory } : LoopState α)
          (loopCompileExp context (context.maxVar + 1) live expression).expression =
        some value := by
    simpa [loopStateOfCrepState] using hloopValue
  simp [evalCrepFullProg, evalCrepFullExps, hvalue,
    crepControlValues, loopCompileProg,
    loopCompileExp.loopCompileExps, loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, evalLoopProgWithCallsAndFfi,
    evalLoopProg, loopReadLocals, loopStateOfCrepState,
    loopResultValues, updateLoopLocal, hcode, hloopValue']

theorem crepToLoop_dec_return_of_empty_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name : Nat) (expression : CrepExp α) (value : α)
    (hcode : (loopCompileExp context (context.maxVar + 1) live expression).code = [])
    (hvalue : evalCrepFullExp state.locals state.memory baseAddress topAddress
      expression = some value)
    (hloopValue : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live expression).expression =
      some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 2) state
      (.dec name expression (.return [.var name]))).map crepControlValues =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 20)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.dec name expression (.return [.var name])))).map
      loopResultValues := by
  have hloopValue' :
      evalLoopExp
          ({ locals := state.locals, globals := state.globals,
             memory := state.memory } : LoopState α)
          (loopCompileExp context (context.maxVar + 1) live expression).expression =
        some value := by
    simpa [loopStateOfCrepState] using hloopValue
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp, hvalue,
    crepControlValues, loopCompileProg, loopCompileExp,
    loopCompileExp.loopCompileExps, loopCompileExps, loopNestedSeq,
    loopTempNames, loopAssignTemps, evalLoopProgWithCallsAndFfi,
    evalLoopProg, evalLoopExp, loopReadLocals, restoreCrepResult,
    loopStateOfCrepState, loopResultValues, updateCrepLocal,
    updateLoopLocal, hcode, hloopValue']

theorem crepToLoop_dec_compose_of_empty_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name : Nat) (expression : CrepExp α) (body : CrepProg α)
    (value : α) (crepResult : CrepControlResult α)
    (loopResult : LoopResult α)
    (hcode : (loopCompileExp context (context.maxVar + 1) live expression).code = [])
    (hnext : (loopCompileExp context (context.maxVar + 1) live expression).nextTemp =
      context.maxVar + 1)
    (hlive : (loopCompileExp context (context.maxVar + 1) live expression).live = live)
    (hvalue : evalCrepFullExp state.locals state.memory baseAddress topAddress
      expression = some value)
    (hloopValue : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live expression).expression =
      some value)
    (hcrepBody : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress (fuel + 1)
      { state with locals := updateCrepLocal state.locals name value } body =
      some crepResult)
    (hloopBody : evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 18)
      { loopStateOfCrepState state with
        locals := updateLoopLocal (loopStateOfCrepState state).locals name value }
      (loopCompileProg
        { context with
          vars := (name, context.maxVar + 1) :: context.vars
          maxVar := context.maxVar + 1 }
        ((context.maxVar + 1) :: live) body) = some loopResult)
    (hresult : crepControlValues
        (restoreCrepResult name (state.locals name) crepResult) =
      loopResultValues loopResult) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 2) state (.dec name expression body)).map crepControlValues =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 20)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.dec name expression body))).map
      loopResultValues := by
  have hloopValue' :
      evalLoopExp
          ({ locals := state.locals, globals := state.globals,
             memory := state.memory } : LoopState α)
          (loopCompileExp context (context.maxVar + 1) live expression).expression =
        some value := by
    simpa [loopStateOfCrepState] using hloopValue
  have hloopBody' :
      evalLoopProgWithCallsAndFfi functions
        (fun _ _ _ _ _ loopState => some loopState) (fuel + 18)
        { locals := updateLoopLocal state.locals name value,
          globals := state.globals, memory := state.memory }
        (loopCompileProg
          { context with
            vars := (name, context.maxVar + 1) :: context.vars
            maxVar := context.maxVar + 1 }
          ((context.maxVar + 1) :: live) body) = some loopResult := by
    simpa [loopStateOfCrepState] using hloopBody
  simp [evalCrepFullProg, hvalue, hcrepBody, crepControlValues,
    restoreCrepResult, loopCompileProg, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, loopStateOfCrepState,
    hcode, hnext, hlive, hloopValue', hloopBody']
  exact hresult

/-!
The assignment case is the first state-transforming Crep-to-Loop boundary.
`loopCompileProg` introduces the same constant assignment after an empty
expression-code prefix; the extra unit of fuel accounts for that generated
sequence node.  The theorem observes the assigned slot rather than equating
the two state representations wholesale, which is the relation consumed by
the later Loop-to-Word proof.
-/
theorem crepToLoop_assign_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name : Nat) (value : α) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.assign name (.const value))).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.assign name (.const value)))).map
        (loopControlLocal name) := by
  simp [evalCrepFullProg, evalCrepFullExp,
    loopStateOfCrepState, updateCrepLocal, updateLoopLocal,
    crepControlLocal, loopCompileProg, loopCompileExp,
    loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopControlLocal]

theorem crepToLoop_assign_var_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name source : Nat) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.assign name (.var source))).map
        (crepControlLocal name) =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.assign name (.var source)))).map
        (loopControlLocal name) := by
  cases hsource : state.locals source with
  | none =>
      simp [evalCrepFullProg, evalCrepFullExp,
        loopStateOfCrepState, loopCompileProg, loopCompileExp,
        loopNestedSeq,
        evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
        hsource]
  | some sourceValue =>
      apply crepToLoop_assign_agreement_of_empty_prefix
        context functions primitive ffi sharedMem baseAddress topAddress fuel
        state live name (.var source) sourceValue
      · simp [loopCompileExp]
      · simp [evalCrepFullExp, hsource]
      · simp [loopStateOfCrepState, loopCompileExp, evalLoopExp, hsource]

theorem crepToLoop_raise_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (exception : α) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.raise exception)).map crepControlException =
    (evalLoopProgWithCallsAndFfi functions
      (fun _ _ _ _ _ loopState => some loopState) (fuel + 8)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.raise exception))).map loopControlException := by
  simp [evalCrepFullProg, crepControlException, loopControlException,
    loopCompileProg, evalLoopProgWithCallsAndFfi, evalLoopProg,
    evalLoopExp, updateLoopLocal]

theorem crepToLoop_call_skip_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.skip : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], (.skip : LoopProg α))) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 4) state (.call none function []) =
      some (.normal state) ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 4)
        (loopStateOfCrepState state)
        (loopCompileProg context live (.call none function [])) =
      some (.normal (loopStateOfCrepState state)) := by
  constructor
  · simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
      assignCrepValues, hcrep]
  · have hskip (n : Nat) (loopState : LoopState α) :
        evalLoopProg (n + 1) loopState (.skip : LoopProg α) =
          some (.normal loopState) := by
      simp [evalLoopProg]
    simp [loopCompileProg, loopCompileExps,
      loopCompileExp.loopCompileExps, loopTempNames, loopAssignTemps,
      loopNestedSeq, evalLoopProgWithCallsAndFfi,
      evalLoopCallWithCallsAndFfi, loopReadLocals, loopBindParameters,
      hcontext, hloop, hskip]

theorem crepToLoop_call_return_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target parameter destination : Nat) (value : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([parameter], (.return [.var parameter] : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 1))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([parameter], (.return [parameter] : LoopProg α))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 8) state
        (.call (some ([destination], none)) function [.const value])).map
        (crepControlLocal destination) =
      (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 8)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.call (some ([destination], none)) function [.const value]))).map
        (loopControlLocal destination) := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    evalCrepFullExp, assignCrepValues, updateCrepLocal,
    crepControlLocal, hcrep, loopCompileProg, loopCompileExps,
    loopCompileExp.loopCompileExps, loopCompileExp_const, loopTempNames,
    loopAssignTemps,
    loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopCallWithCallsAndFfi,
    evalLoopProg, evalLoopExp, loopReadLocals, loopBindParameters,
    loopAssignValues, updateLoopLocal, loopControlLocal, hcontext, hloop]

theorem crepToLoop_call_caught_skip_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat) (exception : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.raise exception : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], loopCompileProg context [] (.raise exception))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 20) state
        (.call (some ([], some (exception, .skip))) function [])).map
        crepControlValues =
      (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 20)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.call (some ([], some (exception, .skip))) function []))).map
        loopResultValues := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    assignCrepValues, crepControlValues, hcrep, loopCompileProg,
    loopCompileExps, loopCompileExp.loopCompileExps, loopTempNames,
    loopAssignTemps, loopNestedSeq, evalLoopProgWithCallsAndFfi,
    evalLoopCallWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopReadLocals, loopBindParameters, updateLoopLocal,
    evalLoopCondition, loopResultValues, hcontext, hloop]

theorem crepToLoop_call_uncaught_raise_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat) (exception : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.raise exception : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], loopCompileProg context [] (.raise exception))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 20) state (.call none function [])).map crepControlException =
      (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 20)
        (loopStateOfCrepState state)
        (loopCompileProg context live (.call none function []))).map
        loopControlException := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    assignCrepValues, crepControlException, hcrep, loopCompileProg,
    loopCompileExps, loopCompileExp.loopCompileExps, loopTempNames,
    loopAssignTemps, loopNestedSeq, evalLoopProgWithCallsAndFfi,
    evalLoopCallWithCallsAndFfi, evalLoopProg, evalLoopExp,
    loopReadLocals, loopBindParameters, updateLoopLocal,
    loopControlException, hcontext, hloop]

theorem crepToLoop_call_caught_return_const_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat) (exception value : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.raise exception : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], loopCompileProg context [] (.raise exception))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 30) state
        (.call (some ([], some (exception, .return [.const value]))) function [])).map
        crepControlValues =
      (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 30)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.call (some ([], some (exception, .return [.const value]))) function []))).map
        loopResultValues := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    evalCrepFullExp, assignCrepValues, crepControlValues, hcrep,
    loopCompileProg, loopCompileExps, loopCompileExp.loopCompileExps,
    loopCompileExp_const, loopTempNames, loopAssignTemps, loopNestedSeq,
    evalLoopProgWithCallsAndFfi, evalLoopCallWithCallsAndFfi, evalLoopProg,
    evalLoopExp, evalLoopCondition, loopReadLocals, loopBindParameters,
    loopAssignValues, updateLoopLocal, loopResultValues, hcontext, hloop]

/-! A caught call may run an arbitrary handler program, including one that
    performs an FFI step.  This boundary theorem leaves the two handler
    executions as explicit hypotheses and relates the observable returned
    values after the caller/callee local restoration performed by each
    evaluator. -/

theorem crepToLoop_call_caught_handler_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (caller : CrepState α) (loopCaller : LoopState α)
    (function : FunName) (target : Nat) (handlerVar : Nat)
    (caught exception : α) (crepBody : CrepProg α) (loopBody : LoopProg α)
    (crepHandler : CrepProg α) (loopHandler : LoopProg α)
    (crepCallee : CrepState α) (loopCallee : LoopState α)
    (crepResult : CrepControlResult α) (loopResult : LoopResult α)
    (hloopCaller : loopCaller = loopStateOfCrepState caller)
    (hcrepLookup : lookupCompiledFunction function crepFunctions =
      some ([], crepBody))
    (hloopLookup : lookupLoopFunction target loopFunctions =
      some ([], loopBody))
    (hcaught : caught == exception)
    (hcrepCallee : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := fun _ => none, memory := caller.memory } crepBody =
      some (.raised crepCallee exception))
    (hloopCallee : evalLoopProgWithCallsAndFfi loopFunctions
      (loopFfiOfCrepFfi ffi) fuel
      { locals := fun _ => none, globals := loopCaller.globals,
        memory := loopCaller.memory } loopBody =
      some (.raised loopCallee exception))
    (hhandler : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := caller.locals, memory := crepCallee.memory } crepHandler =
      some crepResult)
    (hloopHandler : evalLoopProgWithCallsAndFfi loopFunctions
      (loopFfiOfCrepFfi ffi) fuel
      { locals := updateLoopLocal loopCaller.locals handlerVar exception,
        globals := loopCallee.globals, memory := loopCallee.memory } loopHandler =
      some loopResult)
    (hvalues : crepControlValues crepResult = loopResultValues loopResult) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) caller
      (.call (some ([], some (caught, crepHandler))) function [])).map
        crepControlValues =
    (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi)
      (fuel + 2) loopCaller
      (.call (some ([], [])) (some target) []
        (some (handlerVar, loopHandler, .skip, [])))).map
        loopResultValues := by
  subst loopCaller
  have hcrepCall := evalCrepFullCall_caught_handler
    crepFunctions primitive ffi sharedMem baseAddress topAddress fuel caller
    function [] caught crepHandler [] [] [] crepBody
    (fun _ => none) crepCallee exception crepResult
    (by simp [evalCrepFullExps]) hcrepLookup rfl hcrepCallee hcaught hhandler
  have hloopCall : evalLoopCallWithCallsAndFfi loopFunctions
      (loopFfiOfCrepFfi ffi) (fuel + 1) (loopStateOfCrepState caller)
      (some ([], [])) (some target) []
      (some (handlerVar, loopHandler, .skip, [])) =
      some loopResult := by
    simp [evalLoopCallWithCallsAndFfi, hloopLookup,
      loopReadLocals, loopBindParameters, hloopCallee, hloopHandler]
  simp [evalCrepFullProg, hcrepCall, evalLoopProgWithCallsAndFfi,
    hloopCall, hvalues]

theorem crepToLoop_seq_extCall_return_const_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state state' : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (value : α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some state') :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
      (fuel + 20) state
      (.seq (.extCall function configuration configurationLength array arrayLength)
        (.return [.const value]))).map crepControlValues =
    (evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 20)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.seq (.extCall function configuration configurationLength array arrayLength)
          (.return [.const value])))).map loopResultValues := by
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    crepControlValues, evalLoopProgWithCallsAndFfi, evalLoopProg,
    evalLoopExp, loopCompileProg, loopCompileExps,
    loopCompileExp.loopCompileExps, loopCompileExp_const, loopTempNames,
    loopAssignTemps, loopNestedSeq, loopReadLocals, updateLoopLocal,
    loopResultValues, loopFfiOfCrepFfi, crepStateOfLoopState,
    loopStateOfCrepState, hconfiguration, hconfigurationLength, harray,
    harrayLength, hffi]

theorem crepToLoop_extCall_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state state' : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some state') :
    evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 1) state
        (.extCall function configuration configurationLength array arrayLength) =
      some (.normal state') ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 1)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.extCall function configuration configurationLength array arrayLength)) =
      some (.normal (loopStateOfCrepState state')) := by
  constructor
  · exact evalCrepFullProg_extCall crepFunctions primitive ffi sharedMem
      baseAddress topAddress fuel state state' function configuration
      configurationLength array arrayLength configurationValue
      configurationLengthValue arrayValue arrayLengthValue hconfiguration
      hconfigurationLength harray harrayLength hffi
  · rw [evalLoopCompiledExtCall]
    simp [loopFfiOfCrepFfi, crepStateOfLoopState, loopStateOfCrepState,
      hconfiguration, hconfigurationLength, harray, harrayLength, hffi]

/-! An unavailable host service is observable as failure in both evaluators.
    Keeping this equation beside the successful FFI boundary prevents callers
    from accidentally treating the Loop adapter's `none` as a normal state
    transition. -/
theorem crepToLoop_extCall_failure_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = none) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 1) state
        (.extCall function configuration configurationLength array arrayLength) = none ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 1)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.extCall function configuration configurationLength array arrayLength)) = none := by
  constructor
  · simp [evalCrepFullProg, hconfiguration, hconfigurationLength, harray,
      harrayLength, hffi]
  · rw [evalLoopCompiledExtCall]
    simp [loopFfiOfCrepFfi, crepStateOfLoopState, loopStateOfCrepState,
      hconfiguration, hconfigurationLength, harray, harrayLength, hffi]

/-! The pure Crepe-to-Loop adapter deliberately projects terminal FFI events
    away: `evalCrepFullResult` and the legacy Loop evaluator both expose only
    ordinary result values.  The stateful `LoopFfi` boundary retains the event
    separately; this theorem records the compatibility projection explicitly. -/
theorem crepToLoop_extCall_final_projection_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (event : FfiFinalEvent)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some (.final event)) :
    evalCrepFullResult crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 1) state
        (.extCall function configuration configurationLength array arrayLength) = none ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 1)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.extCall function configuration configurationLength array arrayLength)) = none := by
  constructor
  · simp [evalCrepFullResult, evalCrepFullProg, hconfiguration,
      hconfigurationLength, harray, harrayLength, hffi]
  · rw [evalLoopCompiledExtCall]
    simp [loopFfiOfCrepFfi, crepStateOfLoopState, loopStateOfCrepState,
      hconfiguration, hconfigurationLength, harray, harrayLength, hffi]

theorem crepToLoop_seq_extCall_final_projection_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (event : FfiFinalEvent) (second : CrepProg α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some (.final event)) :
    evalCrepFullResult crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 2) state
        (.seq (.extCall function configuration configurationLength array arrayLength)
          second) = none ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi) (fuel + 2)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.seq (.extCall function configuration configurationLength array arrayLength)
            second)) = none := by
  constructor
  · simp [evalCrepFullResult, evalCrepFullProg, hconfiguration,
      hconfigurationLength, harray, harrayLength, hffi]
  · have hfirst := crepToLoop_extCall_final_projection_agreement
      context crepFunctions loopFunctions primitive ffi sharedMem
      baseAddress topAddress fuel state live function configuration
      configurationLength array arrayLength configurationValue
      configurationLengthValue arrayValue arrayLengthValue event
      hconfiguration hconfigurationLength harray harrayLength hffi
    simp [loopCompileProg_seq, evalLoopProgWithCallsAndFfi, hfirst.2]

/-! Failure also short-circuits a continuation.  This is the negative
    sequencing counterpart to `crepToLoop_seq_extCall_agreement`. -/
theorem crepToLoop_seq_extCall_failure_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (second : CrepProg α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = none) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
        baseAddress topAddress (fuel + 2) state
        (.seq (.extCall function configuration configurationLength array arrayLength)
          second) = none ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi)
        (fuel + 2) (loopStateOfCrepState state)
        (loopCompileProg context live
          (.seq (.extCall function configuration configurationLength array arrayLength)
            second)) = none := by
  have hfirst := crepToLoop_extCall_failure_agreement context crepFunctions
    loopFunctions primitive ffi sharedMem baseAddress topAddress fuel state live
    function configuration configurationLength array arrayLength
    configurationValue configurationLengthValue arrayValue arrayLengthValue
    hconfiguration hconfigurationLength harray harrayLength hffi
  constructor
  · simp [evalCrepFullProg, hfirst.1]
  · simp [loopCompileProg_seq, evalLoopProgWithCallsAndFfi, hfirst.2]

/-! Once the first FFI action has been related, sequence evaluation is just
    state-threaded composition.  The continuation hypothesis is deliberately
    arbitrary: this is the reusable boundary needed to grow the complete
    source-to-Loop simulation without reproving the evaluator plumbing for
    every second statement. -/
theorem crepToLoop_seq_extCall_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state state' : CrepState α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configurationValue configurationLengthValue arrayValue arrayLengthValue : α)
    (second : CrepProg α) (result : CrepControlResult α)
    (loopResult : LoopResult α)
    (hconfiguration : state.locals configuration = some configurationValue)
    (hconfigurationLength :
      state.locals configurationLength = some configurationLengthValue)
    (harray : state.locals array = some arrayValue)
    (harrayLength : state.locals arrayLength = some arrayLengthValue)
    (hffi : ffi function configurationValue configurationLengthValue
      arrayValue arrayLengthValue state = some state')
    (hsecond :
      evalCrepFullProg crepFunctions primitive ffi sharedMem
        baseAddress topAddress (fuel + 1) state' second = some result)
    (hloopSecond :
      evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi)
        (fuel + 1) (loopStateOfCrepState state')
        (loopCompileProg context live second) =
        some loopResult) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
        baseAddress topAddress (fuel + 2) state
        (.seq (.extCall function configuration configurationLength array arrayLength)
          second) = some result ∧
    evalLoopProgWithCallsAndFfi loopFunctions (loopFfiOfCrepFfi ffi)
        (fuel + 2) (loopStateOfCrepState state)
        (loopCompileProg context live
          (.seq (.extCall function configuration configurationLength array arrayLength)
            second)) = some loopResult := by
  have hfirst := crepToLoop_extCall_agreement context crepFunctions loopFunctions
    primitive ffi sharedMem baseAddress topAddress fuel state state' live function
    configuration configurationLength array arrayLength configurationValue
    configurationLengthValue arrayValue arrayLengthValue hconfiguration
    hconfigurationLength harray harrayLength hffi
  constructor
  · simp [evalCrepFullProg, hfirst.1, hsecond]
  · simp [loopCompileProg_seq, evalLoopProgWithCallsAndFfi, hfirst.2, hloopSecond]

/-!
The individual constructors above are the executable boundaries used by the
full Crepe-to-Loop proof.  This relation packages their common result shape:
Loop has no terminal-FFI constructor, so a final Crepe FFI event is
intentionally outside the successful simulation relation.
-/
def crepToLoopStateRel (context : LoopContext α)
    (crepState : CrepState α) (loopState : LoopState α) : Prop :=
  loopState.globals = crepState.globals ∧
  loopState.memory = crepState.memory ∧
  ∀ name, name ≤ context.maxVar →
    loopState.locals name = crepState.locals name

def crepToLoopControlRel (context : LoopContext α) :
    CrepControlResult α → LoopResult α → Prop
  | .normal crepState, .normal loopState =>
      crepToLoopStateRel context crepState loopState
  | .returned crepState values, .returned loopState loopValues =>
      crepToLoopStateRel context crepState loopState ∧ values = loopValues
  | .raised crepState exception, .raised loopState loopException =>
      crepToLoopStateRel context crepState loopState ∧ exception = loopException
  | .broke crepState label, .broke loopState loopLabel =>
      crepToLoopStateRel context crepState loopState ∧ label = loopLabel
  | .continued crepState label, .continued loopState loopLabel =>
      crepToLoopStateRel context crepState loopState ∧ label = loopLabel
  | _, _ => False

/-!
Primitive-aware source-to-Loop correctness boundary.  The legacy
CrepToLoopProgramCorrect below predates the combined Loop evaluator and is
kept for existing proofs; this boundary makes primitive execution
non-vacuous by threading the primitive handler into the Loop semantics.
-/
def CrepToLoopProgramCorrectWithPrimitive
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : CrepProg α) : Prop :=
  ∀ (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (crepFunctions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α)
    (sourceFuel targetFuel : Nat)
    (state : CrepState α) (live : List Nat)
    (crepResult : CrepControlResult α) (loopResult : LoopResult α),
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (sourceFuel + 1) state program =
        some crepResult →
    evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) targetFuel (loopStateOfCrepState state)
      (loopCompileProg context live program) = some loopResult →
    crepToLoopControlRel context crepResult loopResult

theorem mapM_eq_loopReadLocals (locals : Nat → Option α) (arguments : List Nat) :
    arguments.mapM locals = loopReadLocals locals arguments := by
  induction arguments with
  | nil => rfl
  | cons argument arguments ih =>
      simp [loopReadLocals, ih]

theorem crepToLoopProgramCorrectWithPrimitive_primitive
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (names : List Nat) (operator : PrimOp) (arguments : List Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.primitive names operator arguments : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  have hread := mapM_eq_loopReadLocals state.locals arguments
  have hfold (base : Nat → Option α) (entries : List (Nat × α)) :
      List.foldl (fun locals entry =>
        updateCrepLocal locals entry.fst entry.snd) base entries =
      List.foldl (fun locals entry =>
        updateLoopLocal locals entry.fst entry.snd) base entries := by
    induction entries generalizing base with
    | nil => rfl
    | cons entry entries ih =>
        cases entry with
        | mk name value =>
            simp only [List.foldl]
            rw [show updateCrepLocal base name value =
              updateLoopLocal base name value by rfl]
            exact ih _
  cases targetFuel with
  | zero =>
      simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases hargs : loopReadLocals state.locals arguments with
      | none =>
          simp [evalCrepFullProg, hread, hargs,
            assignCrepValues] at hcrep hloop
      | some values =>
          cases hprimitive : primitive operator values with
          | none =>
              simp [evalCrepFullProg, hread, hargs,
                hprimitive, assignCrepValues] at hcrep hloop
          | some result =>
              by_cases hlength : names.length = result.length
              · simp [evalCrepFullProg, loopCompileProg,
                  evalLoopProgWithPrimitiveCallsAndFfi, hread, hargs,
                  hprimitive, hlength, hfold, assignCrepValues,
                  loopAssignValues, loopStateOfCrepState] at hcrep hloop
                cases hcrep
                cases hloop
                simp [crepToLoopControlRel, crepToLoopStateRel]
              · simp [evalCrepFullProg, hread, hargs,
                hprimitive, hlength, hfold, assignCrepValues] at hcrep hloop

theorem crepToLoopWithPrimitive_assign_agreement_of_empty_prefix
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (name : Nat) (expression : CrepExp α) (value : α)
    (hcode : (loopCompileExp context (context.maxVar + 1) live expression).code = [])
    (hvalue : evalCrepFullExp state.locals state.memory baseAddress topAddress expression =
      some value)
    (heval : evalLoopExp (loopStateOfCrepState state)
      (loopCompileExp context (context.maxVar + 1) live expression).expression =
      some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.assign name expression)).map
        (crepControlLocal name) =
    (evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live (.assign name expression))).map
        (loopControlLocal name) := by
  have heval' : evalLoopExp
      ({ locals := state.locals, globals := state.globals,
         memory := state.memory } : LoopState α)
      (loopCompileExp context (context.maxVar + 1) live expression).expression =
      some value := by
    simpa [loopStateOfCrepState] using heval
  simp [evalCrepFullProg, hvalue,
    loopCompileProg, hcode, loopNestedSeq,
    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
    loopStateOfCrepState, updateCrepLocal,
    crepControlLocal]
  rw [heval']
  simp [loopControlLocal, updateLoopLocal]

theorem crepToLoop_call_skip_primitive_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.skip : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], (.skip : LoopProg α))) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 4) state (.call none function []) =
      some (.normal state) ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
        (loopFfiOfCrepFfi ffi) (fuel + 4)
        (loopStateOfCrepState state)
        (loopCompileProg context live (.call none function [])) =
      some (.normal (loopStateOfCrepState state)) := by
  constructor
  · simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
      assignCrepValues, hcrep]
  · have hskip (n : Nat) (loopState : LoopState α) :
        evalLoopProg (n + 1) loopState (.skip : LoopProg α) =
          some (.normal loopState) := by
      simp [evalLoopProg]
    simp [loopCompileProg, loopCompileExps,
      loopCompileExp.loopCompileExps, loopTempNames, loopAssignTemps,
      loopNestedSeq, evalLoopProgWithPrimitiveCallsAndFfi,
      evalLoopCallWithPrimitiveCallsAndFfi, loopReadLocals,
      loopBindParameters, hcontext, hloop, hskip]

theorem crepToLoop_call_return_const_primitive_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target parameter destination : Nat) (value : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([parameter], (.return [.var parameter] : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 1))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([parameter], (.return [parameter] : LoopProg α))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 8) state
        (.call (some ([destination], none)) function [.const value])).map
        (crepControlLocal destination) =
      (evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
        (loopFfiOfCrepFfi ffi) (fuel + 8)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.call (some ([destination], none)) function [.const value]))).map
        (loopControlLocal destination) := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    evalCrepFullExp, assignCrepValues, updateCrepLocal,
    crepControlLocal, hcrep, loopCompileProg, loopCompileExps,
    loopCompileExp.loopCompileExps, loopCompileExp_const, loopTempNames,
    loopAssignTemps, loopNestedSeq,
    evalLoopProgWithPrimitiveCallsAndFfi,
    evalLoopCallWithPrimitiveCallsAndFfi, evalLoopProg, evalLoopExp,
    loopReadLocals, loopBindParameters, loopAssignValues, updateLoopLocal,
    loopControlLocal, hcontext, hloop]

theorem crepToLoop_call_caught_skip_primitive_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat) (exception : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.raise exception : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], loopCompileProg context [] (.raise exception))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 20) state
        (.call (some ([], some (exception, .skip))) function [])).map
        crepControlValues =
      (evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
        (loopFfiOfCrepFfi ffi) (fuel + 20)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.call (some ([], some (exception, .skip))) function []))).map
        loopResultValues := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    assignCrepValues, crepControlValues, hcrep, loopCompileProg,
    loopCompileExps, loopCompileExp.loopCompileExps, loopTempNames,
    loopAssignTemps, loopNestedSeq,
    evalLoopProgWithPrimitiveCallsAndFfi,
    evalLoopCallWithPrimitiveCallsAndFfi, evalLoopProg, evalLoopExp,
    loopReadLocals, loopBindParameters, updateLoopLocal,
    evalLoopCondition, loopResultValues, hcontext, hloop]

theorem crepToLoop_call_uncaught_raise_primitive_agreement
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat) (exception : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.raise exception : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], loopCompileProg context [] (.raise exception))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 20) state (.call none function [])).map crepControlException =
      (evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
        (loopFfiOfCrepFfi ffi) (fuel + 20)
        (loopStateOfCrepState state)
        (loopCompileProg context live (.call none function []))).map
        loopControlException := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    assignCrepValues, crepControlException, hcrep, loopCompileProg,
    loopCompileExps, loopCompileExp.loopCompileExps, loopTempNames,
    loopAssignTemps, loopNestedSeq,
    evalLoopProgWithPrimitiveCallsAndFfi,
    evalLoopCallWithPrimitiveCallsAndFfi, evalLoopProg, evalLoopExp,
    loopReadLocals, loopBindParameters, updateLoopLocal,
    loopControlException, hcontext, hloop]

theorem crepToLoop_call_caught_return_const_primitive_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (function : FunName)
    (target : Nat) (exception value : α)
    (hcrep : lookupCompiledFunction function crepFunctions =
      some ([], (.raise exception : CrepProg α)))
    (hcontext : lookupInfo function context.functions = some (target, 0))
    (hloop : lookupLoopFunction target loopFunctions =
      some ([], loopCompileProg context [] (.raise exception))) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem baseAddress topAddress
        (fuel + 30) state
        (.call (some ([], some (exception, .return [.const value]))) function [])).map
        crepControlValues =
      (evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
        (loopFfiOfCrepFfi ffi) (fuel + 30)
        (loopStateOfCrepState state)
        (loopCompileProg context live
          (.call (some ([], some (exception, .return [.const value]))) function []))).map
        loopResultValues := by
  simp [evalCrepFullProg, evalCrepFullCall, evalCrepFullExps,
    evalCrepFullExp, assignCrepValues, crepControlValues, hcrep,
    loopCompileProg, loopCompileExps, loopCompileExp.loopCompileExps,
    loopCompileExp_const, loopTempNames, loopAssignTemps, loopNestedSeq,
    evalLoopProgWithPrimitiveCallsAndFfi,
    evalLoopCallWithPrimitiveCallsAndFfi, evalLoopProg, evalLoopExp,
    evalLoopCondition, loopReadLocals, loopBindParameters,
    loopAssignValues, updateLoopLocal, loopResultValues, hcontext, hloop]

theorem crepToLoop_call_caught_handler_primitive_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (caller : CrepState α) (loopCaller : LoopState α)
    (function : FunName) (target : Nat) (handlerVar : Nat)
    (caught exception : α) (crepBody : CrepProg α) (loopBody : LoopProg α)
    (crepHandler : CrepProg α) (loopHandler : LoopProg α)
    (crepCallee : CrepState α) (loopCallee : LoopState α)
    (crepResult : CrepControlResult α) (loopResult : LoopResult α)
    (hloopCaller : loopCaller = loopStateOfCrepState caller)
    (hcrepLookup : lookupCompiledFunction function crepFunctions =
      some ([], crepBody))
    (hloopLookup : lookupLoopFunction target loopFunctions =
      some ([], loopBody))
    (hcaught : caught == exception)
    (hcrepCallee : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := fun _ => none, memory := caller.memory } crepBody =
      some (.raised crepCallee exception))
    (hloopCallee : evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
      (loopFfiOfCrepFfi ffi) fuel
      { locals := fun _ => none, globals := loopCaller.globals,
        memory := loopCaller.memory } loopBody =
      some (.raised loopCallee exception))
    (hhandler : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := caller.locals, memory := crepCallee.memory } crepHandler =
      some crepResult)
    (hloopHandler : evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
      (loopFfiOfCrepFfi ffi) fuel
      { locals := updateLoopLocal loopCaller.locals handlerVar exception,
        globals := loopCallee.globals, memory := loopCallee.memory } loopHandler =
      some loopResult)
    (hvalues : crepControlValues crepResult = loopResultValues loopResult) :
    (evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) caller
      (.call (some ([], some (caught, crepHandler))) function [])).map
        crepControlValues =
    (evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
      (loopFfiOfCrepFfi ffi) (fuel + 2) loopCaller
      (.call (some ([], [])) (some target) []
        (some (handlerVar, loopHandler, .skip, [])))).map
        loopResultValues := by
  subst loopCaller
  have hcrepCall := evalCrepFullCall_caught_handler
    crepFunctions primitive ffi sharedMem baseAddress topAddress fuel caller
    function [] caught crepHandler [] [] [] crepBody
    (fun _ => none) crepCallee exception crepResult
    (by simp [evalCrepFullExps]) hcrepLookup rfl hcrepCallee hcaught hhandler
  have hloopCall : evalLoopCallWithPrimitiveCallsAndFfi primitive loopFunctions
      (loopFfiOfCrepFfi ffi) (fuel + 1) (loopStateOfCrepState caller)
      (some ([], [])) (some target) []
      (some (handlerVar, loopHandler, .skip, [])) =
      some loopResult := by
    simp [evalLoopCallWithPrimitiveCallsAndFfi, hloopLookup,
      loopReadLocals, loopBindParameters, hloopCallee, hloopHandler]
  simp [evalCrepFullProg, hcrepCall,
    evalLoopProgWithPrimitiveCallsAndFfi, hloopCall, hvalues]

theorem crepToLoopWithPrimitive_shMem_store_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (hoperator : operator = .store ∨ operator = .store8 ∨
      operator = .store16 ∨ operator = .store32)
    (hvalue : state.locals name = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htargetMemory : targetState.memory address = some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.shMem operator name (.const address))).map
        (crepControlMemoryAt address) =
    (evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.shMem operator name (.const address)))).map
        (loopControlMemoryAt address) := by
  rcases hoperator with rfl | rfl | rfl | rfl <;>
    simp [evalCrepFullProg, evalCrepFullExp, hshared,
      crepControlMemoryAt, loopControlMemoryAt,
      loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg, evalLoopExp,
      loopStateOfCrepState, updateLoopMemory, hvalue,
      htargetMemory]

theorem crepToLoopWithPrimitive_shMem_load_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (hoperator : operator = .load ∨ operator = .load8 ∨
      operator = .load16 ∨ operator = .load32)
    (hmemory : state.memory address = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htargetLocal : targetState.locals name = some value) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.shMem operator name (.const address))).map
        (crepControlLocal name) =
    (evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.shMem operator name (.const address)))).map
        (loopControlLocal name) := by
  rcases hoperator with rfl | rfl | rfl | rfl <;>
    simp [evalCrepFullProg, evalCrepFullExp, hmemory, hshared,
      crepControlLocal, loopControlLocal,
      loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg, evalLoopExp,
      loopStateOfCrepState, updateLoopLocal, htargetLocal]

theorem crepToLoopWithPrimitive_shMem_store_state_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (hoperator : operator = .store ∨ operator = .store8 ∨
      operator = .store16 ∨ operator = .store32)
    (hvalue : state.locals name = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htarget : targetState =
      { state with memory := updateMemory state.memory address value }) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.shMem operator name (.const address)) =
        some (.normal targetState) ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.shMem operator name (.const address))) =
        some (.normal (loopStateOfCrepState targetState)) := by
  rcases hoperator with rfl | rfl | rfl | rfl
  all_goals
    subst targetState
    have hmemoryUpdate : updateLoopMemory state.memory address value =
        updateMemory state.memory address value := by
      funext current
      by_cases h : address = current
      · subst current
        simp [updateLoopMemory, updateMemory]
      · have h' : current ≠ address := Ne.symm h
        simp [updateLoopMemory, updateMemory, h, h']
    simp [evalCrepFullProg, evalCrepFullExp, hshared,
      loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg, evalLoopExp,
      loopStateOfCrepState, hvalue, hmemoryUpdate]

theorem crepToLoopWithPrimitive_shMem_load_state_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (hoperator : operator = .load ∨ operator = .load8 ∨
      operator = .load16 ∨ operator = .load32)
    (hmemory : state.memory address = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htarget : targetState =
      { state with locals := updateCrepLocal state.locals name value }) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.shMem operator name (.const address)) =
        some (.normal targetState) ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 2)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.shMem operator name (.const address))) =
        some (.normal (loopStateOfCrepState targetState)) := by
  rcases hoperator with rfl | rfl | rfl | rfl
  all_goals
    subst targetState
    have hlocalUpdate : updateLoopLocal state.locals name value =
        updateCrepLocal state.locals name value := by
      rfl
    simp [evalCrepFullProg, evalCrepFullExp, hmemory, hshared,
      loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg, evalLoopExp,
      loopStateOfCrepState, hlocalUpdate]

theorem crepToLoopWithPrimitive_seq_normal_compose_loop_extra_live_pre
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state middle : CrepState α) (live : List Nat)
    (first second : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hfirst : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state first = some (.normal middle))
    (hloopFirst : evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
      loopFfi (fuel + 2) (loopStateOfCrepState state)
      (loopCompileProg context live first) =
      some (.normal (loopStateOfCrepState middle)))
    (hsecond : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) middle second = some result)
    (hloopSecond : evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
      loopFfi (fuel + 2) (loopStateOfCrepState middle)
      (loopCompileProg context live second) = some loopResult) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state (.seq first second) = some result ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions loopFfi
      (fuel + 3) (loopStateOfCrepState state)
      (loopCompileProg context live (.seq first second)) =
      some loopResult := by
  constructor
  · simp [evalCrepFullProg, hfirst, hsecond]
  · simp [loopCompileProg_seq, evalLoopProgWithPrimitiveCallsAndFfi,
      hloopFirst, hloopSecond]

theorem crepToLoopWithPrimitive_shMem_store_seq_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (second : CrepProg α) (result : CrepControlResult α)
    (loopResult : LoopResult α)
    (hoperator : operator = .store ∨ operator = .store8 ∨
      operator = .store16 ∨ operator = .store32)
    (hvalue : state.locals name = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htarget : targetState =
      { state with memory := updateMemory state.memory address value })
    (hsecond : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) targetState second = some result)
    (hloopSecond : evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 2)
      (loopStateOfCrepState targetState)
      (loopCompileProg context live second) = some loopResult) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 2) state
      (.seq (.shMem operator name (.const address)) second) = some result ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 3)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.seq (.shMem operator name (.const address)) second)) =
      some loopResult := by
  have hfirst := crepToLoopWithPrimitive_shMem_store_state_agreement
    context functions primitive ffi sharedMem baseAddress topAddress fuel
    state targetState live operator name address value hoperator hvalue hshared
    htarget
  exact crepToLoopWithPrimitive_seq_normal_compose_loop_extra_live_pre
    context [] functions primitive ffi (loopFfiOfCrepFfi ffi) sharedMem
    baseAddress topAddress fuel state targetState live
    (.shMem operator name (.const address)) second result loopResult
    hfirst.1 hfirst.2 hsecond hloopSecond

theorem crepToLoopWithPrimitive_shMem_load_seq_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state targetState : CrepState α) (live : List Nat)
    (operator : CrepMemOp) (name : Nat) (address value : α)
    (second : CrepProg α) (result : CrepControlResult α)
    (loopResult : LoopResult α)
    (hoperator : operator = .load ∨ operator = .load8 ∨
      operator = .load16 ∨ operator = .load32)
    (hmemory : state.memory address = some value)
    (hshared : sharedMem operator name address state = some targetState)
    (htarget : targetState =
      { state with locals := updateCrepLocal state.locals name value })
    (hsecond : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) targetState second = some result)
    (hloopSecond : evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 2)
      (loopStateOfCrepState targetState)
      (loopCompileProg context live second) = some loopResult) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 2) state
      (.seq (.shMem operator name (.const address)) second) = some result ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 3)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.seq (.shMem operator name (.const address)) second)) =
      some loopResult := by
  have hfirst := crepToLoopWithPrimitive_shMem_load_state_agreement
    context functions primitive ffi sharedMem baseAddress topAddress fuel
    state targetState live operator name address value hoperator hmemory hshared
    htarget
  exact crepToLoopWithPrimitive_seq_normal_compose_loop_extra_live_pre
    context [] functions primitive ffi (loopFfiOfCrepFfi ffi) sharedMem
    baseAddress topAddress fuel state targetState live
    (.shMem operator name (.const address)) second result loopResult
    hfirst.1 hfirst.2 hsecond hloopSecond

theorem crepToLoopProgramCorrectWithPrimitive_skip
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    CrepToLoopProgramCorrectWithPrimitive (.skip : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      simp [loopCompileProg, evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      cases hloop
      simp [crepToLoopControlRel, crepToLoopStateRel, loopStateOfCrepState]

theorem crepToLoopProgramCorrectWithPrimitive_tick
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    CrepToLoopProgramCorrectWithPrimitive (.tick : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      simp [loopCompileProg, evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      cases hloop
      simp [crepToLoopControlRel, crepToLoopStateRel, loopStateOfCrepState]

theorem crepToLoopProgramCorrectWithPrimitive_break
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (label : Nat) :
    CrepToLoopProgramCorrectWithPrimitive (.break label) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      simp [loopCompileProg, evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      cases hloop
      simp [crepToLoopControlRel, crepToLoopStateRel, loopStateOfCrepState]

theorem crepToLoopProgramCorrectWithPrimitive_continue
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (label : Nat) :
    CrepToLoopProgramCorrectWithPrimitive (.continue label) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      simp [loopCompileProg, evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      cases hloop
      simp [crepToLoopControlRel, crepToLoopStateRel, loopStateOfCrepState]

theorem crepToLoopProgramCorrectWithPrimitive_raise
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : α) :
    CrepToLoopProgramCorrectWithPrimitive (.raise exception) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          simp [loopCompileProg, evalLoopProgWithPrimitiveCallsAndFfi,
            evalLoopProg, evalLoopExp, updateLoopLocal] at hloop
          cases hloop
          simp [crepToLoopControlRel, crepToLoopStateRel,
            loopStateOfCrepState]
          intro name hname
          have htemp : context.maxVar + 1 ≠ name := by omega
          have htemp' : name ≠ context.maxVar + 1 := Ne.symm htemp
          simp [updateLoopLocal, htemp']

theorem crepToLoopProgramCorrectWithPrimitive_return_nil
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    CrepToLoopProgramCorrectWithPrimitive (.return [] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopNestedSeq, loopTempNames,
            loopAssignTemps, evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          simp [loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopNestedSeq, loopTempNames,
            loopAssignTemps, evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          cases hloop
          simp [crepToLoopControlRel, crepToLoopStateRel,
            loopStateOfCrepState]

theorem crepToLoopProgramCorrectWithPrimitive_assign_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : Nat) (value : α) :
    CrepToLoopProgramCorrectWithPrimitive (.assign name (.const value)) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
            evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
            evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
            evalLoopExp] at hloop
          cases hloop
          simp [crepToLoopControlRel, crepToLoopStateRel,
            loopStateOfCrepState, updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrectWithPrimitive_assign_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name source : Nat) :
    CrepToLoopProgramCorrectWithPrimitive (.assign name (.var source) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hsource : state.locals source with
  | none => simp [hsource] at hcrep
  | some value =>
      simp [hsource] at hcrep
      subst crepResult
      cases targetFuel with
      | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithPrimitiveCallsAndFfi,
                loopStateOfCrepState] at hloop
          | succ targetFuel =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                evalLoopExp, loopStateOfCrepState, hsource] at hloop
              cases hloop
              simp [crepToLoopControlRel, crepToLoopStateRel,
                updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrectWithPrimitive_assign_load_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name source : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.load (.var source)) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hsource : state.locals source with
  | none => simp [hsource] at hcrep
  | some address =>
      cases hmemory : state.memory address with
      | none => simp [hsource, hmemory] at hcrep
      | some value =>
          simp [hsource, hmemory] at hcrep
          subst crepResult
          cases targetFuel with
          | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi,
                    loopStateOfCrepState] at hloop
              | succ targetFuel =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, loopStateOfCrepState, hsource, hmemory] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrectWithPrimitive_return_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (value : α) :
    CrepToLoopProgramCorrectWithPrimitive
      (.return [.const value] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopTempNames,
            loopAssignTemps, evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp.loopCompileExps,
                loopCompileExp, loopCompileExps, loopNestedSeq,
                loopTempNames, loopAssignTemps,
                evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                loopReadLocals, loopStateOfCrepState] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, loopReadLocals, loopStateOfCrepState,
                    updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega
              | succ targetFuel =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, loopReadLocals, loopStateOfCrepState,
                    updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega

theorem crepToLoopProgramCorrectWithPrimitive_store_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : α) :
    CrepToLoopProgramCorrectWithPrimitive
      (.store (.const address) (.const value) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
            evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, updateLoopLocal] at hloop
                  cases hloop
                  simp only [crepToLoopControlRel, crepToLoopStateRel]
                  constructor
                  · rfl
                  · constructor
                    · funext current
                      by_cases h : current = address
                      · subst current
                        simp [updateLoopMemory, updateMemory]
                      · have h' : address ≠ current := Ne.symm h
                        simp [loopStateOfCrepState, updateLoopMemory,
                          updateMemory, h, h']
                    · intro name hname
                      have htemp : name ≠ context.maxVar + 1 := by omega
                      simp [loopStateOfCrepState, updateLoopLocal, htemp]
              | succ targetFuel =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, updateLoopLocal] at hloop
                  cases hloop
                  simp only [crepToLoopControlRel, crepToLoopStateRel]
                  constructor
                  · rfl
                  · constructor
                    · funext current
                      by_cases h : current = address
                      · subst current
                        simp [updateLoopMemory, updateMemory]
                      · have h' : address ≠ current := Ne.symm h
                        simp [loopStateOfCrepState, updateLoopMemory,
                          updateMemory, h, h']
                    · intro name hname
                      have htemp : name ≠ context.maxVar + 1 := by omega
                      simp [loopStateOfCrepState, updateLoopLocal, htemp]

theorem crepToLoopProgramCorrectWithPrimitive_store_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address : α) (source : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.store (.const address) (.var source) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hsource : state.locals source with
  | none => simp [hsource] at hcrep
  | some value =>
      simp [hsource] at hcrep
      subst crepResult
      cases targetFuel with
      | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                        evalLoopExp, loopStateOfCrepState, updateLoopLocal,
                        hsource] at hloop
                      cases hloop
                      simp only [crepToLoopControlRel, crepToLoopStateRel]
                      constructor
                      · trivial
                      · constructor
                        · funext current
                          by_cases h : current = address
                          · subst current
                            simp [updateLoopMemory, updateMemory]
                          · have h' : address ≠ current := Ne.symm h
                            simp [updateLoopMemory,
                              updateMemory, h, h']
                        · intro name hname
                          have htemp : name ≠ context.maxVar + 1 := by omega
                          simp [updateLoopLocal, htemp]
                  | succ targetFuel =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                        evalLoopExp, loopStateOfCrepState, updateLoopLocal,
                        hsource] at hloop
                      cases hloop
                      simp only [crepToLoopControlRel, crepToLoopStateRel]
                      constructor
                      · trivial
                      · constructor
                        · funext current
                          by_cases h : current = address
                          · subst current
                            simp [updateLoopMemory, updateMemory]
                          · have h' : address ≠ current := Ne.symm h
                            simp [updateLoopMemory,
                              updateMemory, h, h']
                        · intro name hname
                          have htemp : name ≠ context.maxVar + 1 := by omega
                          simp [updateLoopLocal, htemp]

theorem crepToLoopProgramCorrectWithPrimitive_store32_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : α) :
    CrepToLoopProgramCorrectWithPrimitive
      (.store32 (.const address) (.const value) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
            evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                        evalLoopExp, updateLoopLocal] at hloop
                      cases hloop
                      simp only [crepToLoopControlRel, crepToLoopStateRel]
                      constructor
                      · rfl
                      · constructor
                        · funext current
                          by_cases h : current = address
                          · subst current
                            simp [updateLoopMemory, updateMemory]
                          · have h' : address ≠ current := Ne.symm h
                            simp [loopStateOfCrepState, updateLoopMemory,
                              updateMemory, h, h']
                        · intro name hname
                          have htemp : name ≠ context.maxVar + 1 := by omega
                          have htemp' : name ≠ context.maxVar + 2 := by omega
                          simp [loopStateOfCrepState, updateLoopLocal,
                            htemp, htemp']
                  | succ targetFuel =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                        evalLoopExp, updateLoopLocal] at hloop
                      cases hloop
                      simp only [crepToLoopControlRel, crepToLoopStateRel]
                      constructor
                      · rfl
                      · constructor
                        · funext current
                          by_cases h : current = address
                          · subst current
                            simp [updateLoopMemory, updateMemory]
                          · have h' : address ≠ current := Ne.symm h
                            simp [loopStateOfCrepState, updateLoopMemory,
                              updateMemory, h, h']
                        · intro name hname
                          have htemp : name ≠ context.maxVar + 1 := by omega
                          have htemp' : name ≠ context.maxVar + 2 := by omega
                          simp [loopStateOfCrepState, updateLoopLocal,
                            htemp, htemp']

theorem crepToLoopProgramCorrectWithPrimitive_storeByte_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : α) :
    CrepToLoopProgramCorrectWithPrimitive
      (.storeByte (.const address) (.const value) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
            evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                        evalLoopExp, updateLoopLocal] at hloop
                      cases hloop
                      simp only [crepToLoopControlRel, crepToLoopStateRel]
                      constructor
                      · rfl
                      · constructor
                        · funext current
                          by_cases h : current = address
                          · subst current
                            simp [updateLoopMemory, updateMemory]
                          · have h' : address ≠ current := Ne.symm h
                            simp [loopStateOfCrepState, updateLoopMemory,
                              updateMemory, h, h']
                        · intro name hname
                          have htemp : name ≠ context.maxVar + 1 := by omega
                          have htemp' : name ≠ context.maxVar + 2 := by omega
                          simp [loopStateOfCrepState, updateLoopLocal,
                            htemp, htemp']
                  | succ targetFuel =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                        evalLoopExp, updateLoopLocal] at hloop
                      cases hloop
                      simp only [crepToLoopControlRel, crepToLoopStateRel]
                      constructor
                      · rfl
                      · constructor
                        · funext current
                          by_cases h : current = address
                          · subst current
                            simp [updateLoopMemory, updateMemory]
                          · have h' : address ≠ current := Ne.symm h
                            simp [loopStateOfCrepState, updateLoopMemory,
                              updateMemory, h, h']
                        · intro name hname
                          have htemp : name ≠ context.maxVar + 1 := by omega
                          have htemp' : name ≠ context.maxVar + 2 := by omega
                          simp [loopStateOfCrepState, updateLoopLocal,
                            htemp, htemp']

theorem crepToLoopProgramCorrectWithPrimitive_assign_load32_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : Nat) (address : α) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.load32 (.const address)) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hmemory : state.memory address with
  | none => simp [hmemory] at hcrep
  | some value =>
      simp [hmemory] at hcrep
      subst crepResult
      cases targetFuel with
      | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                        evalLoopExp] at hloop
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                            evalLoopExp, updateLoopLocal,
                            loopStateOfCrepState, hmemory] at hloop
                          cases hloop
                          simp only [crepToLoopControlRel, crepToLoopStateRel]
                          constructor
                          · simp
                          · constructor
                            · simp
                            · intro current hcurrent
                              have htemp : current ≠ context.maxVar + 1 := by omega
                              simp [updateCrepLocal, updateLoopLocal, htemp]
                      | succ targetFuel =>
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                            evalLoopExp, updateLoopLocal,
                            loopStateOfCrepState, hmemory] at hloop
                          cases hloop
                          simp only [crepToLoopControlRel, crepToLoopStateRel]
                          constructor
                          · simp
                          · constructor
                            · simp
                            · intro current hcurrent
                              have htemp : current ≠ context.maxVar + 1 := by omega
                              simp [updateCrepLocal, updateLoopLocal, htemp]

theorem crepToLoopProgramCorrectWithPrimitive_assign_load32_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name source : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.load32 (.var source)) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hsource : state.locals source with
  | none => simp [hsource] at hcrep
  | some address =>
      cases hmemory : state.memory address with
      | none => simp [hsource, hmemory] at hcrep
      | some value =>
          simp [hsource, hmemory] at hcrep
          subst crepResult
          cases targetFuel with
          | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg] at hloop
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                            evalLoopExp, loopStateOfCrepState, hsource] at hloop
                      | succ targetFuel =>
                          have hloopSource :
                              (loopStateOfCrepState state).locals source = some address := by
                            simpa [loopStateOfCrepState] using hsource
                          have hloopMemory :
                              (loopStateOfCrepState state).memory address = some value := by
                            simpa [loopStateOfCrepState] using hmemory
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                            evalLoopExp, updateLoopLocal,
                            loopStateOfCrepState, hsource, hmemory] at hloop
                          cases hloop
                          simp only [crepToLoopControlRel, crepToLoopStateRel]
                          constructor
                          · trivial
                          · constructor
                            · trivial
                            · intro current hcurrent
                              have htemp : current ≠ context.maxVar + 1 := by omega
                              simp [updateCrepLocal, updateLoopLocal, htemp]

theorem crepToLoopProgramCorrectWithPrimitive_assign_loadByte_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name source : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.loadByte (.var source)) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hsource : state.locals source with
  | none => simp [hsource] at hcrep
  | some address =>
      cases hmemory : state.memory address with
      | none => simp [hsource, hmemory] at hcrep
      | some value =>
          simp [hsource, hmemory] at hcrep
          subst crepResult
          cases targetFuel with
          | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg] at hloop
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                            evalLoopExp, loopStateOfCrepState, hsource] at hloop
                      | succ targetFuel =>
                          have hloopSource :
                              (loopStateOfCrepState state).locals source = some address := by
                            simpa [loopStateOfCrepState] using hsource
                          have hloopMemory :
                              (loopStateOfCrepState state).memory address = some value := by
                            simpa [loopStateOfCrepState] using hmemory
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                            evalLoopExp, updateLoopLocal,
                            loopStateOfCrepState, hsource, hmemory] at hloop
                          cases hloop
                          simp only [crepToLoopControlRel, crepToLoopStateRel]
                          constructor
                          · trivial
                          · constructor
                            · trivial
                            · intro current hcurrent
                              have htemp : current ≠ context.maxVar + 1 := by omega
                              simp [updateCrepLocal, updateLoopLocal, htemp]

theorem crepToLoopProgramCorrectWithPrimitive_assign_loadByte_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : Nat) (address : α) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.loadByte (.const address)) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hmemory : state.memory address with
  | none => simp [hmemory] at hcrep
  | some value =>
      simp [hmemory] at hcrep
      subst crepResult
      cases targetFuel with
      | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                        evalLoopExp] at hloop
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                            evalLoopExp, updateLoopLocal,
                            loopStateOfCrepState, hmemory] at hloop
                          cases hloop
                          simp only [crepToLoopControlRel, crepToLoopStateRel]
                          constructor
                          · simp
                          · constructor
                            · simp
                            · intro current hcurrent
                              have htemp : current ≠ context.maxVar + 1 := by omega
                              simp [updateCrepLocal, updateLoopLocal, htemp]
                      | succ targetFuel =>
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                            evalLoopExp, updateLoopLocal,
                            loopStateOfCrepState, hmemory] at hloop
                          cases hloop
                          simp only [crepToLoopControlRel, crepToLoopStateRel]
                          constructor
                          · simp
                          · constructor
                            · simp
                            · intro current hcurrent
                              have htemp : current ≠ context.maxVar + 1 := by omega
                              simp [updateCrepLocal, updateLoopLocal, htemp]

theorem crepToLoopProgramCorrectWithPrimitive_assign_add_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : Nat) (left right : α) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.op .add [.const left, .const right]) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp, evalPanBinOp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp,
            evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          simp [loopCompileProg, loopCompileExp,
            loopCompileExp.loopCompileExps, loopNestedSeq,
            evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
            evalLoopExp] at hloop
          cases hloop
          simp [crepToLoopControlRel, crepToLoopStateRel,
            loopStateOfCrepState, updateCrepLocal, updateLoopLocal,
            evalLoopBinOp]

theorem crepToLoopProgramCorrectWithPrimitive_assign_add_var_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name left right : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.op .add [.var left, .var right]) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hleft : state.locals left with
  | none => simp [hleft] at hcrep
  | some leftValue =>
      cases hright : state.locals right with
      | none => simp [hleft, hright] at hcrep
      | some rightValue =>
          simp [hleft, hright, evalPanBinOp] at hcrep
          subst crepResult
          cases targetFuel with
          | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp,
                    evalLoopProgWithPrimitiveCallsAndFfi] at hloop
              | succ targetFuel =>
                  have hloopLeft :
                      (loopStateOfCrepState state).locals left = some leftValue := by
                    simpa [loopStateOfCrepState] using hleft
                  have hloopRight :
                      (loopStateOfCrepState state).locals right = some rightValue := by
                    simpa [loopStateOfCrepState] using hright
                  simp [loopCompileProg, loopCompileExp,
                    loopCompileExp.loopCompileExps, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, evalLoopBinOp] at hloop
                  simp [hloopLeft, hloopRight] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    loopStateOfCrepState, updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrectWithPrimitive_assign_sub_var_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name left right : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.op .sub [.var left, .var right]) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hleft : state.locals left with
  | none => simp [hleft] at hcrep
  | some leftValue =>
      cases hright : state.locals right with
      | none => simp [hleft, hright] at hcrep
      | some rightValue =>
          simp [hleft, hright, evalPanBinOp] at hcrep
          subst crepResult
          cases targetFuel with
          | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp,
                    evalLoopProgWithPrimitiveCallsAndFfi] at hloop
              | succ targetFuel =>
                  have hloopLeft :
                      (loopStateOfCrepState state).locals left = some leftValue := by
                    simpa [loopStateOfCrepState] using hleft
                  have hloopRight :
                      (loopStateOfCrepState state).locals right = some rightValue := by
                    simpa [loopStateOfCrepState] using hright
                  simp [loopCompileProg, loopCompileExp,
                    loopCompileExp.loopCompileExps, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, evalLoopBinOp] at hloop
                  simp [hloopLeft, hloopRight] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    loopStateOfCrepState, updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrectWithPrimitive_assign_and_var_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name left right : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.op .and [.var left, .var right]) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hleft : state.locals left with
  | none => simp [hleft] at hcrep
  | some leftValue =>
      cases hright : state.locals right with
      | none => simp [hleft, hright] at hcrep
      | some rightValue =>
          simp [hleft, hright, evalPanBinOp] at hcrep
          subst crepResult
          cases targetFuel with
          | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp,
                    evalLoopProgWithPrimitiveCallsAndFfi] at hloop
              | succ targetFuel =>
                  have hloopLeft :
                      (loopStateOfCrepState state).locals left = some leftValue := by
                    simpa [loopStateOfCrepState] using hleft
                  have hloopRight :
                      (loopStateOfCrepState state).locals right = some rightValue := by
                    simpa [loopStateOfCrepState] using hright
                  simp [loopCompileProg, loopCompileExp,
                    loopCompileExp.loopCompileExps, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, evalLoopBinOp] at hloop
                  simp [hloopLeft, hloopRight] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    loopStateOfCrepState, updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrectWithPrimitive_assign_or_var_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name left right : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.op .or [.var left, .var right]) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hleft : state.locals left with
  | none => simp [hleft] at hcrep
  | some leftValue =>
      cases hright : state.locals right with
      | none => simp [hleft, hright] at hcrep
      | some rightValue =>
          simp [hleft, hright, evalPanBinOp] at hcrep
          subst crepResult
          cases targetFuel with
          | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp,
                    evalLoopProgWithPrimitiveCallsAndFfi] at hloop
              | succ targetFuel =>
                  have hloopLeft :
                      (loopStateOfCrepState state).locals left = some leftValue := by
                    simpa [loopStateOfCrepState] using hleft
                  have hloopRight :
                      (loopStateOfCrepState state).locals right = some rightValue := by
                    simpa [loopStateOfCrepState] using hright
                  simp [loopCompileProg, loopCompileExp,
                    loopCompileExp.loopCompileExps, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, evalLoopBinOp] at hloop
                  simp [hloopLeft, hloopRight] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    loopStateOfCrepState, updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrectWithPrimitive_assign_xor_var_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name left right : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.op .xor [.var left, .var right]) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hleft : state.locals left with
  | none => simp [hleft] at hcrep
  | some leftValue =>
      cases hright : state.locals right with
      | none => simp [hleft, hright] at hcrep
      | some rightValue =>
          simp [hleft, hright, evalPanBinOp] at hcrep
          subst crepResult
          cases targetFuel with
          | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp,
                    evalLoopProgWithPrimitiveCallsAndFfi] at hloop
              | succ targetFuel =>
                  have hloopLeft :
                      (loopStateOfCrepState state).locals left = some leftValue := by
                    simpa [loopStateOfCrepState] using hleft
                  have hloopRight :
                      (loopStateOfCrepState state).locals right = some rightValue := by
                    simpa [loopStateOfCrepState] using hright
                  simp [loopCompileProg, loopCompileExp,
                    loopCompileExp.loopCompileExps, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, evalLoopBinOp] at hloop
                  simp [hloopLeft, hloopRight] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    loopStateOfCrepState, updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrectWithPrimitive_assign_lsl_var_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name left right : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.shift .lsl (.var left) (.var right)) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hleft : state.locals left with
  | none => simp [hleft] at hcrep
  | some leftValue =>
      cases hright : state.locals right with
      | none => simp [hleft, hright] at hcrep
      | some rightValue =>
          simp [hleft, hright, evalPanShift] at hcrep
          subst crepResult
          cases targetFuel with
          | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp,
                    evalLoopProgWithPrimitiveCallsAndFfi] at hloop
              | succ targetFuel =>
                  have hloopLeft :
                      (loopStateOfCrepState state).locals left = some leftValue := by
                    simpa [loopStateOfCrepState] using hleft
                  have hloopRight :
                      (loopStateOfCrepState state).locals right = some rightValue := by
                    simpa [loopStateOfCrepState] using hright
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, evalLoopShift] at hloop
                  simp [hloopLeft, hloopRight] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    loopStateOfCrepState, updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrectWithPrimitive_assign_lsr_var_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name left right : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.shift .lsr (.var left) (.var right)) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hleft : state.locals left with
  | none => simp [hleft] at hcrep
  | some leftValue =>
      cases hright : state.locals right with
      | none => simp [hleft, hright] at hcrep
      | some rightValue =>
          simp [hleft, hright, evalPanShift] at hcrep
          subst crepResult
          cases targetFuel with
          | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp,
                    evalLoopProgWithPrimitiveCallsAndFfi] at hloop
              | succ targetFuel =>
                  have hloopLeft :
                      (loopStateOfCrepState state).locals left = some leftValue := by
                    simpa [loopStateOfCrepState] using hleft
                  have hloopRight :
                      (loopStateOfCrepState state).locals right = some rightValue := by
                    simpa [loopStateOfCrepState] using hright
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, evalLoopShift] at hloop
                  simp [hloopLeft, hloopRight] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    loopStateOfCrepState, updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrectWithPrimitive_assign_sub_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : Nat) (left right : α) :
    CrepToLoopProgramCorrectWithPrimitive
      (.assign name (.op .sub [.const left, .const right]) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp, evalPanBinOp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp,
            evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          simp [loopCompileProg, loopCompileExp,
            loopCompileExp.loopCompileExps, loopNestedSeq,
            evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
            evalLoopExp, evalLoopBinOp] at hloop
          cases hloop
          simp [crepToLoopControlRel, crepToLoopStateRel,
            loopStateOfCrepState, updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrectWithPrimitive_return_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (source : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.return [.var source] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp] at hcrep
  cases hsource : state.locals source with
  | none => simp [hsource] at hcrep
  | some value =>
      simp [hsource] at hcrep
      subst crepResult
      cases targetFuel with
      | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp.loopCompileExps,
                loopCompileExps, loopTempNames, loopAssignTemps,
                evalLoopProgWithPrimitiveCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    loopReadLocals, loopStateOfCrepState] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp.loopCompileExps,
                        loopCompileExp, loopCompileExps, loopNestedSeq,
                        loopTempNames, loopAssignTemps,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                        evalLoopExp, loopReadLocals, loopStateOfCrepState,
                        updateLoopLocal, hsource] at hloop
                      cases hloop
                      simp [crepToLoopControlRel, crepToLoopStateRel,
                        updateLoopLocal]
                      intro name hname htemp
                      omega
                  | succ targetFuel =>
                      simp [loopCompileProg, loopCompileExp.loopCompileExps,
                        loopCompileExp, loopCompileExps, loopNestedSeq,
                        loopTempNames, loopAssignTemps,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                        evalLoopExp, loopReadLocals, loopStateOfCrepState,
                        updateLoopLocal, hsource] at hloop
                      cases hloop
                      simp [crepToLoopControlRel, crepToLoopStateRel,
                        updateLoopLocal]
                      intro name hname htemp
                      omega

theorem crepToLoopProgramCorrectWithPrimitive_return_add_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (left right : α) :
    CrepToLoopProgramCorrectWithPrimitive
      (.return [.op .add [.const left, .const right]] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    evalPanBinOp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopTempNames, loopAssignTemps,
            evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp.loopCompileExps,
                loopCompileExp, loopCompileExps, loopNestedSeq,
                loopTempNames, loopAssignTemps,
                evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, evalLoopBinOp, loopReadLocals,
                    loopStateOfCrepState, updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega
              | succ targetFuel =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, evalLoopBinOp, loopReadLocals,
                    loopStateOfCrepState, updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega

theorem crepToLoopProgramCorrectWithPrimitive_return_sub_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (left right : α) :
    CrepToLoopProgramCorrectWithPrimitive
      (.return [.op .sub [.const left, .const right]] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    evalPanBinOp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopTempNames, loopAssignTemps,
            evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp.loopCompileExps,
                loopCompileExp, loopCompileExps, loopNestedSeq,
                loopTempNames, loopAssignTemps,
                evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, evalLoopBinOp, loopReadLocals,
                    loopStateOfCrepState, updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega
              | succ targetFuel =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, evalLoopBinOp, loopReadLocals,
                    loopStateOfCrepState, updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega

theorem crepToLoopProgramCorrectWithPrimitive_return_mul_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (left right : α) :
    CrepToLoopProgramCorrectWithPrimitive
      (.return [.crepOp .mul [.const left, .const right]] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp] at hcrep
  subst crepResult
  have hargs :
      loopCompileExp.loopCompileExps context (context.maxVar + 1) live
        [.const left, .const right] =
      { expressions := [.const left, .const right], code := [],
        nextTemp := context.maxVar + 1, live := live } := by
    rw [loopCompileExp.loopCompileExps.eq_2, loopCompileExp.eq_1,
      loopCompileExp.loopCompileExps.eq_2, loopCompileExp.eq_1,
      loopCompileExp.loopCompileExps.eq_1]
    rfl
  have hargsExpressions :
      (loopCompileExp.loopCompileExps context (context.maxVar + 1) live
        [.const left, .const right]).expressions =
        [.const left, .const right] := by
    simpa using congrArg (fun result => result.expressions) hargs
  have hmulExp :
      loopCompileExp context (context.maxVar + 1) live
        (.crepOp .mul [.const left, .const right]) =
      { code :=
          [.assign (context.maxVar + 1) (.const left),
           .assign (context.maxVar + 1 + 1) (.const right),
           .arith (.longMul (context.maxVar + 1 + 1 + 1)
             (context.maxVar + 1 + 1 + 1) (context.maxVar + 1)
             (context.maxVar + 1 + 1))],
        expression := .var (context.maxVar + 1 + 1 + 1),
        nextTemp := context.maxVar + 1 + 1 + 1 + 1,
        live := (context.maxVar + 1 + 1 + 1) :: (context.maxVar + 1) ::
          (context.maxVar + 1 + 1) :: live } := by
    rw [loopCompileExp.eq_8 (context := context)
      (tmp := context.maxVar + 1) (live := live)
      (arguments := [.const left, .const right])
      (left := .const left) (right := .const right) hargsExpressions]
    simp [hargs]
  cases targetFuel with
  | zero => simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [hmulExp, loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopTempNames, loopAssignTemps,
            evalLoopProgWithPrimitiveCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [hmulExp, loopCompileProg, loopCompileExp.loopCompileExps,
                loopCompileExps, loopNestedSeq, loopTempNames,
                loopAssignTemps, evalLoopProgWithPrimitiveCallsAndFfi,
                evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [hmulExp, loopCompileProg,
                    loopCompileExp.loopCompileExps, loopCompileExps,
                    loopNestedSeq, loopTempNames, loopAssignTemps,
                    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                    evalLoopExp, loopReadLocals,
                    loopStateOfCrepState] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [hmulExp, loopCompileProg,
                        loopCompileExp.loopCompileExps, loopCompileExps,
                        loopNestedSeq, loopTempNames, loopAssignTemps,
                        evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg,
                        evalLoopExp, loopReadLocals,
                        loopStateOfCrepState] at hloop
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [hmulExp, loopCompileProg,
                            loopCompileExp.loopCompileExps,
                            loopCompileExps, loopNestedSeq, loopTempNames,
                            loopAssignTemps,
                            evalLoopProgWithPrimitiveCallsAndFfi,
                            evalLoopProg, evalLoopExp, loopReadLocals,
                            loopStateOfCrepState, updateLoopLocal] at hloop
                      | succ targetFuel =>
                          simp [hmulExp, loopCompileProg,
                            loopCompileExp.loopCompileExps,
                            loopCompileExps, loopNestedSeq, loopTempNames,
                            loopAssignTemps,
                            evalLoopProgWithPrimitiveCallsAndFfi,
                            evalLoopProg, evalLoopExp, loopReadLocals,
                            loopStateOfCrepState, updateLoopLocal] at hloop
                          cases hloop
                          simp [crepToLoopControlRel, crepToLoopStateRel,
                            updateLoopLocal]
                          intro name hname
                          have h1 : name ≠ context.maxVar + 1 := by omega
                          have h2 : name ≠ context.maxVar + 1 + 1 := by omega
                          have h3 : name ≠ context.maxVar + 1 + 1 + 1 := by omega
                          have h4 : name ≠ context.maxVar + 1 + 1 + 1 + 1 := by omega
                          simp [h1, h2, h3, h4]

theorem crepToLoopProgramCorrectWithPrimitive_extCall
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    CrepToLoopProgramCorrectWithPrimitive
      (.extCall function configuration configurationLength array arrayLength :
        CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  cases hc : state.locals configuration with
  | none => simp [hc] at hcrep
  | some configurationValue =>
      cases hcl : state.locals configurationLength with
      | none => simp [hc, hcl] at hcrep
      | some configurationLengthValue =>
          cases ha : state.locals array with
          | none => simp [hc, hcl, ha] at hcrep
          | some arrayValue =>
              cases hal : state.locals arrayLength with
              | none => simp [hc, hcl, ha, hal] at hcrep
              | some arrayLengthValue =>
                  cases hffi : ffi function configurationValue
                      configurationLengthValue arrayValue arrayLengthValue state with
                  | none => simp [hc, hcl, ha, hal, hffi] at hcrep
                  | some ffiResult =>
                      cases ffiResult with
                      | returned state' =>
                          simp [hc, hcl, ha, hal, hffi] at hcrep
                          subst crepResult
                          have hffi' :
                              ffi function configurationValue configurationLengthValue
                                arrayValue arrayLengthValue
                                ({ locals := state.locals, memory := state.memory,
                                   globals := state.globals } :
                                  CrepState α) = some (.returned state') := by
                            simpa using hffi
                          cases targetFuel with
                          | zero =>
                              simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
                          | succ targetFuel =>
                              simp [loopCompileProg] at hloop
                              rw [evalLoopProgWithPrimitiveCallsAndFfi_ffi] at hloop
                              simp [loopFfiOfCrepFfi, crepStateOfLoopState,
                                loopStateOfCrepState, hc, hcl, ha, hal,
                                hffi'] at hloop
                              cases hloop
                              simp [crepToLoopControlRel, crepToLoopStateRel]
                      | final event =>
                          simp [hc, hcl, ha, hal, hffi] at hcrep
                          have hffi' :
                              ffi function configurationValue configurationLengthValue
                                arrayValue arrayLengthValue
                                ({ locals := state.locals, memory := state.memory,
                                   globals := state.globals } :
                                  CrepState α) = some (.final event) := by
                            simpa using hffi
                          cases targetFuel with
                          | zero =>
                              simp [evalLoopProgWithPrimitiveCallsAndFfi] at hloop
                          | succ targetFuel =>
                              simp [loopCompileProg] at hloop
                              rw [evalLoopProgWithPrimitiveCallsAndFfi_ffi] at hloop
                              simp [loopFfiOfCrepFfi, crepStateOfLoopState,
                                loopStateOfCrepState, hc, hcl, ha, hal,
                                hffi'] at hloop

theorem crepToLoopWithPrimitive_seq_normal_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state middle : CrepState α) (live : List Nat)
    (first second : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hfirst : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state first = some (.normal middle))
    (hloopFirst : evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
      loopFfi (fuel + 1) (loopStateOfCrepState state)
      (loopCompileProg context live first) =
      some (.normal (loopStateOfCrepState middle)))
    (hsecond : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) middle second = some result)
    (hloopSecond : evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
      loopFfi (fuel + 1) (loopStateOfCrepState middle)
      (loopCompileProg context live second) = some loopResult) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state (.seq first second) = some result ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions loopFfi
      (fuel + 2) (loopStateOfCrepState state)
      (loopCompileProg context live (.seq first second)) =
      some loopResult := by
  constructor
  · simp [evalCrepFullProg, hfirst, hsecond]
  · simp [loopCompileProg_seq, evalLoopProgWithPrimitiveCallsAndFfi,
      hloopFirst, hloopSecond]

theorem crepToLoopWithPrimitive_seq_terminal_compose
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (first second : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hfirst : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state first = some result)
    (hloopFirst : evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
      loopFfi (fuel + 1) (loopStateOfCrepState state)
      (loopCompileProg context live first) = some loopResult)
    (hcrepTerminal : ∀ middle : CrepState α, result ≠ .normal middle)
    (hloopTerminal : ∀ middle : LoopState α, loopResult ≠ .normal middle) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state (.seq first second) = some result ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions loopFfi
      (fuel + 2) (loopStateOfCrepState state)
      (loopCompileProg context live (.seq first second)) = some loopResult := by
  constructor
  · simp only [evalCrepFullProg]
    rw [hfirst]
    cases result with
    | normal middle => exact (hcrepTerminal middle rfl).elim
    | returned state values => rfl
    | raised state exception => rfl
    | broke state label => rfl
    | continued state label => rfl
    | finalFfi state event => rfl
  · simp only [loopCompileProg_seq, evalLoopProgWithPrimitiveCallsAndFfi]
    rw [hloopFirst]
    cases loopResult with
    | normal middle => exact (hloopTerminal middle rfl).elim
    | returned state values => rfl
    | raised state exception => rfl
    | broke state label => rfl
    | continued state label => rfl

theorem crepToLoopWithPrimitive_seq_normal_compose_loop_extra
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state middle : CrepState α) (first second : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hfirst : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state first = some (.normal middle))
    (hloopFirst : evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
      loopFfi (fuel + 2) (loopStateOfCrepState state)
      (loopCompileProg context [] first) =
      some (.normal (loopStateOfCrepState middle)))
    (hsecond : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) middle second = some result)
    (hloopSecond : evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
      loopFfi (fuel + 2) (loopStateOfCrepState middle)
      (loopCompileProg context [] second) = some loopResult) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state (.seq first second) = some result ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions loopFfi
      (fuel + 3) (loopStateOfCrepState state)
      (loopCompileProg context [] (.seq first second)) =
      some loopResult := by
  constructor
  · simp [evalCrepFullProg, hfirst, hsecond]
  · simp [loopCompileProg_seq, evalLoopProgWithPrimitiveCallsAndFfi,
      hloopFirst, hloopSecond]

theorem crepToLoopWithPrimitive_seq_terminal_compose_loop_extra
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (crepFunctions : List (CompiledFunction α))
    (loopFunctions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (loopFfi : FunName → α → α → α → α → LoopState α → Option (LoopState α))
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (first second : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hfirst : evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) state first = some result)
    (hloopFirst : evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions
      loopFfi (fuel + 2) (loopStateOfCrepState state)
      (loopCompileProg context [] first) = some loopResult)
    (hcrepTerminal : ∀ middle : CrepState α, result ≠ .normal middle)
    (hloopTerminal : ∀ middle : LoopState α, loopResult ≠ .normal middle) :
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (fuel + 2) state (.seq first second) = some result ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive loopFunctions loopFfi
      (fuel + 3) (loopStateOfCrepState state)
      (loopCompileProg context [] (.seq first second)) =
      some loopResult := by
  constructor
  · simp only [evalCrepFullProg]
    rw [hfirst]
    cases result with
    | normal middle => exact (hcrepTerminal middle rfl).elim
    | returned state values => rfl
    | raised state exception => rfl
    | broke state label => rfl
    | continued state label => rfl
    | finalFfi state event => rfl
  · simp only [loopCompileProg_seq, evalLoopProgWithPrimitiveCallsAndFfi]
    rw [hloopFirst]
    cases loopResult with
    | normal middle => exact (hloopTerminal middle rfl).elim
    | returned state values => rfl
    | raised state exception => rfl
    | broke state label => rfl
    | continued state label => rfl

theorem crepToLoopWithPrimitive_while_const_zero_agreement
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat) (name : Nat)
    (body : CrepProg α)
    (hname : name ≠ context.maxVar + 1) :
    (evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state (.while (.const (by exact 0)) body)).map
        (crepControlLocal name) =
    (evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 12)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.while (.const (by exact 0)) body))).map
        (loopControlLocal name) := by
  simp [evalCrepFullProg, evalCrepFullExp,
    loopStateOfCrepState, crepControlLocal, loopControlLocal,
    loopCompileProg, loopCompileExp, loopNestedSeq,
    evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg, evalLoopExp,
    evalLoopRepeatWithPrimitiveCallsAndFfi,
    evalLoopCondition, updateLoopLocal, hname]

theorem crepToLoopWithPrimitive_ite_const_zero_compose
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (thenBranch elseBranch : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hcrepElse : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress fuel state elseBranch = some result)
    (hloopElse : evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 2)
      { loopStateOfCrepState state with
        locals := updateLoopLocal (loopStateOfCrepState state).locals
          (context.maxVar + 1) 0 }
      (loopCompileProg context live elseBranch) = some loopResult) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state
      (.ite (.const (by exact 0)) thenBranch elseBranch) = some result ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 5)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.ite (.const (by exact 0)) thenBranch elseBranch)) =
      some loopResult := by
  constructor
  · simp [evalCrepFullProg, evalCrepFullExp, hcrepElse]
  · simp [loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg, evalLoopExp,
      evalLoopCondition, updateLoopLocal, hloopElse]

theorem crepToLoopWithPrimitive_ite_const_one_compose
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (state : CrepState α) (live : List Nat)
    (thenBranch elseBranch : CrepProg α)
    (result : CrepControlResult α) (loopResult : LoopResult α)
    (hone : (1 : α) ≠ 0)
    (hcrepThen : evalCrepFullProg [] primitive ffi sharedMem
      baseAddress topAddress fuel state thenBranch = some result)
    (hloopThen : evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 2)
      { loopStateOfCrepState state with
        locals := updateLoopLocal (loopStateOfCrepState state).locals
          (context.maxVar + 1) 1 }
      (loopCompileProg context live thenBranch) = some loopResult) :
    evalCrepFullProg [] primitive ffi sharedMem baseAddress topAddress
      (fuel + 1) state
      (.ite (.const (by exact 1)) thenBranch elseBranch) = some result ∧
    evalLoopProgWithPrimitiveCallsAndFfi primitive functions
      (loopFfiOfCrepFfi ffi) (fuel + 5)
      (loopStateOfCrepState state)
      (loopCompileProg context live
        (.ite (.const (by exact 1)) thenBranch elseBranch)) =
      some loopResult := by
  constructor
  · simp [evalCrepFullProg, evalCrepFullExp, hone, hcrepThen]
  · simp [loopCompileProg, loopCompileExp, loopNestedSeq,
      evalLoopProgWithPrimitiveCallsAndFfi, evalLoopProg, evalLoopExp,
      evalLoopCondition, updateLoopLocal, hone, hloopThen]

/-!
CrepToLoopProgramCorrect is the complete-pass induction boundary.  It keeps
the source and target fuel bounds independent because lowering introduces
temporary sequences whose cost depends on the constructor and expression
shape.  Constructor lemmas therefore supply the exact fuel inequalities they
need, while the assembled predicate records the resulting control/state
simulation uniformly.
-/
def CrepToLoopProgramCorrect
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : CrepProg α) : Prop :=
  ∀ (context : LoopContext α)
    (functions : List (Nat × List Nat × LoopProg α))
    (crepFunctions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α)
    (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α)
    (sourceFuel targetFuel : Nat)
    (state : CrepState α) (live : List Nat)
    (crepResult : CrepControlResult α) (loopResult : LoopResult α),
    evalCrepFullProg crepFunctions primitive ffi sharedMem
      baseAddress topAddress (sourceFuel + 1) state program =
        some crepResult →
    evalLoopProgWithCallsAndFfi functions (loopFfiOfCrepFfi ffi)
      targetFuel (loopStateOfCrepState state)
      (loopCompileProg context live program) = some loopResult →
    crepToLoopControlRel context crepResult loopResult

theorem crepToLoopProgramCorrect_skip
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    CrepToLoopProgramCorrect (.skip : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      simp [loopCompileProg, evalLoopProgWithCallsAndFfi] at hloop
      cases hloop
      simp [crepToLoopControlRel, crepToLoopStateRel, loopStateOfCrepState]

theorem crepToLoopProgramCorrect_tick
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    CrepToLoopProgramCorrect (.tick : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      simp [loopCompileProg, evalLoopProgWithCallsAndFfi] at hloop
      cases hloop
      simp [crepToLoopControlRel, crepToLoopStateRel, loopStateOfCrepState]

theorem crepToLoopProgramCorrect_break
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (label : Nat) :
    CrepToLoopProgramCorrect (.break label) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      simp [loopCompileProg, evalLoopProgWithCallsAndFfi] at hloop
      cases hloop
      simp [crepToLoopControlRel, crepToLoopStateRel, loopStateOfCrepState]

theorem crepToLoopProgramCorrect_continue
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (label : Nat) :
    CrepToLoopProgramCorrect (.continue label) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      simp [loopCompileProg, evalLoopProgWithCallsAndFfi] at hloop
      cases hloop
      simp [crepToLoopControlRel, crepToLoopStateRel, loopStateOfCrepState]

theorem crepToLoopProgramCorrect_raise
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : α) :
    CrepToLoopProgramCorrect (.raise exception) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          simp [loopCompileProg, evalLoopProgWithCallsAndFfi,
            evalLoopProg, evalLoopExp, updateLoopLocal] at hloop
          cases hloop
          simp [crepToLoopControlRel, crepToLoopStateRel,
            loopStateOfCrepState]
          intro name hname
          have htemp : context.maxVar + 1 ≠ name := by omega
          have htemp' : name ≠ context.maxVar + 1 := Ne.symm htemp
          simp [updateLoopLocal, htemp']

theorem crepToLoopProgramCorrect_return_nil
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    CrepToLoopProgramCorrect (.return [] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopNestedSeq, loopTempNames,
            loopAssignTemps, evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          simp [loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopNestedSeq, loopTempNames,
            loopAssignTemps, evalLoopProgWithCallsAndFfi] at hloop
          cases hloop
          simp [crepToLoopControlRel, crepToLoopStateRel,
            loopStateOfCrepState]

theorem crepToLoopProgramCorrect_assign_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : Nat) (value : α) :
    CrepToLoopProgramCorrect (.assign name (.const value)) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
            evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
            evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp] at hloop
          cases hloop
          simp [crepToLoopControlRel, crepToLoopStateRel,
            loopStateOfCrepState, updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrect_assign_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name source : Nat) :
    CrepToLoopProgramCorrect (.assign name (.var source) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hsource : state.locals source with
  | none => simp [hsource] at hcrep
  | some value =>
      simp [hsource] at hcrep
      subst crepResult
      cases targetFuel with
      | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithCallsAndFfi, loopStateOfCrepState] at hloop
          | succ targetFuel =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                loopStateOfCrepState, hsource] at hloop
              cases hloop
              simp [crepToLoopControlRel, crepToLoopStateRel,
                updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrect_return_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (value : α) :
    CrepToLoopProgramCorrect (.return [.const value] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopTempNames,
            loopAssignTemps, evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp.loopCompileExps,
                loopCompileExp, loopCompileExps, loopNestedSeq,
                loopTempNames, loopAssignTemps,
                evalLoopProgWithCallsAndFfi, evalLoopProg,
                loopReadLocals, loopStateOfCrepState] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                    loopReadLocals, loopStateOfCrepState, updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega
              | succ targetFuel =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                    loopReadLocals, loopStateOfCrepState, updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega

theorem crepToLoopProgramCorrect_return_add_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (left right : α) :
    CrepToLoopProgramCorrect
      (.return [.op .add [.const left, .const right]] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    evalPanBinOp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopTempNames, loopAssignTemps,
            evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp.loopCompileExps,
                loopCompileExp, loopCompileExps, loopNestedSeq,
                loopTempNames, loopAssignTemps,
                evalLoopProgWithCallsAndFfi, evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                    evalLoopBinOp, loopReadLocals, loopStateOfCrepState,
                    updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega
              | succ targetFuel =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                    evalLoopBinOp, loopReadLocals, loopStateOfCrepState,
                    updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega

theorem crepToLoopProgramCorrect_return_sub_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (left right : α) :
    CrepToLoopProgramCorrect
      (.return [.op .sub [.const left, .const right]] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp,
    evalPanBinOp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopTempNames, loopAssignTemps,
            evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp.loopCompileExps,
                loopCompileExp, loopCompileExps, loopNestedSeq,
                loopTempNames, loopAssignTemps,
                evalLoopProgWithCallsAndFfi, evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                    evalLoopBinOp, loopReadLocals, loopStateOfCrepState,
                    updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega
              | succ targetFuel =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                    evalLoopBinOp, loopReadLocals, loopStateOfCrepState,
                    updateLoopLocal] at hloop
                  cases hloop
                  simp [crepToLoopControlRel, crepToLoopStateRel,
                    updateLoopLocal]
                  intro name hname htemp
                  omega

theorem crepToLoopProgramCorrect_return_mul_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (left right : α) :
    CrepToLoopProgramCorrect
      (.return [.crepOp .mul [.const left, .const right]] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp] at hcrep
  subst crepResult
  have hargs :
      loopCompileExp.loopCompileExps context (context.maxVar + 1) live
        [.const left, .const right] =
      { expressions := [.const left, .const right], code := [],
        nextTemp := context.maxVar + 1, live := live } := by
    rw [loopCompileExp.loopCompileExps.eq_2, loopCompileExp.eq_1,
      loopCompileExp.loopCompileExps.eq_2, loopCompileExp.eq_1,
      loopCompileExp.loopCompileExps.eq_1]
    rfl
  have hargsExpressions :
      (loopCompileExp.loopCompileExps context (context.maxVar + 1) live
        [.const left, .const right]).expressions =
        [.const left, .const right] := by
    simpa using congrArg (fun result => result.expressions) hargs
  have hmulExp :
      loopCompileExp context (context.maxVar + 1) live
        (.crepOp .mul [.const left, .const right]) =
      { code :=
          [.assign (context.maxVar + 1) (.const left),
           .assign (context.maxVar + 1 + 1) (.const right),
           .arith (.longMul (context.maxVar + 1 + 1 + 1)
             (context.maxVar + 1 + 1 + 1) (context.maxVar + 1)
             (context.maxVar + 1 + 1))],
        expression := .var (context.maxVar + 1 + 1 + 1),
        nextTemp := context.maxVar + 1 + 1 + 1 + 1,
        live := (context.maxVar + 1 + 1 + 1) :: (context.maxVar + 1) ::
          (context.maxVar + 1 + 1) :: live } := by
    rw [loopCompileExp.eq_8 (context := context)
      (tmp := context.maxVar + 1) (live := live)
      (arguments := [.const left, .const right])
      (left := .const left) (right := .const right) hargsExpressions]
    simp [hargs]
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [hmulExp, loopCompileProg, loopCompileExp.loopCompileExps,
            loopCompileExps, loopTempNames, loopAssignTemps,
            evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [hmulExp, loopCompileProg, loopCompileExp.loopCompileExps,
                loopCompileExps, loopNestedSeq,
                loopTempNames, loopAssignTemps,
                evalLoopProgWithCallsAndFfi, evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [hmulExp, loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                    loopReadLocals, loopStateOfCrepState] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [hmulExp, loopCompileProg,
                        loopCompileExp.loopCompileExps,
                        loopCompileExps, loopNestedSeq, loopTempNames,
                        loopAssignTemps, evalLoopProgWithCallsAndFfi,
                        evalLoopProg, evalLoopExp, loopReadLocals,
                        loopStateOfCrepState] at hloop
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [hmulExp, loopCompileProg,
                            loopCompileExp.loopCompileExps,
                            loopCompileExps, loopNestedSeq, loopTempNames,
                            loopAssignTemps, evalLoopProgWithCallsAndFfi,
                            evalLoopProg, evalLoopExp, loopReadLocals,
                            loopStateOfCrepState, updateLoopLocal] at hloop
                      | succ targetFuel =>
                          simp [hmulExp, loopCompileProg,
                            loopCompileExp.loopCompileExps,
                            loopCompileExps, loopNestedSeq, loopTempNames,
                            loopAssignTemps, evalLoopProgWithCallsAndFfi,
                            evalLoopProg, evalLoopExp, loopReadLocals,
                            loopStateOfCrepState, updateLoopLocal] at hloop
                          cases hloop
                          simp [crepToLoopControlRel, crepToLoopStateRel,
                            updateLoopLocal]
                          intro name hname
                          have h1 : name ≠ context.maxVar + 1 := by omega
                          have h2 : name ≠ context.maxVar + 1 + 1 := by omega
                          have h3 : name ≠ context.maxVar + 1 + 1 + 1 := by omega
                          have h4 : name ≠ context.maxVar + 1 + 1 + 1 + 1 := by omega
                          simp [h1, h2, h3, h4]

theorem crepToLoopProgramCorrect_return_var
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (source : Nat) :
    CrepToLoopProgramCorrect (.return [.var source] : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExps, evalCrepFullExp] at hcrep
  cases hsource : state.locals source with
  | none => simp [hsource] at hcrep
  | some value =>
      simp [hsource] at hcrep
      subst crepResult
      cases targetFuel with
      | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp.loopCompileExps,
                loopCompileExps, loopTempNames, loopAssignTemps,
                evalLoopProgWithCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp.loopCompileExps,
                    loopCompileExp, loopCompileExps, loopNestedSeq,
                    loopTempNames, loopAssignTemps,
                    evalLoopProgWithCallsAndFfi, evalLoopProg,
                    loopReadLocals, loopStateOfCrepState] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp.loopCompileExps,
                        loopCompileExp, loopCompileExps, loopNestedSeq,
                        loopTempNames, loopAssignTemps,
                        evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                        loopReadLocals, loopStateOfCrepState,
                        updateLoopLocal, hsource] at hloop
                      cases hloop
                      simp [crepToLoopControlRel, crepToLoopStateRel,
                        updateLoopLocal]
                      intro name hname htemp
                      omega
                  | succ targetFuel =>
                      simp [loopCompileProg, loopCompileExp.loopCompileExps,
                        loopCompileExp, loopCompileExps, loopNestedSeq,
                        loopTempNames, loopAssignTemps,
                        evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                        loopReadLocals, loopStateOfCrepState,
                        updateLoopLocal, hsource] at hloop
                      cases hloop
                      simp [crepToLoopControlRel, crepToLoopStateRel,
                        updateLoopLocal]
                      intro name hname htemp
                      omega

theorem crepToLoopProgramCorrect_store_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : α) :
    CrepToLoopProgramCorrect (.store (.const address) (.const value) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
            evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithCallsAndFfi, evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                    updateLoopLocal] at hloop
                  cases hloop
                  simp only [crepToLoopControlRel, crepToLoopStateRel]
                  constructor
                  · rfl
                  · constructor
                    · funext current
                      by_cases h : current = address
                      · subst current
                        simp [updateLoopMemory, updateMemory]
                      · have h' : address ≠ current := Ne.symm h
                        simp [loopStateOfCrepState, updateLoopMemory, updateMemory,
                          h, h']
                    · intro name hname
                      have htemp : name ≠ context.maxVar + 1 := by omega
                      simp [loopStateOfCrepState, updateLoopLocal, htemp]
              | succ targetFuel =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                    updateLoopLocal] at hloop
                  cases hloop
                  simp only [crepToLoopControlRel, crepToLoopStateRel]
                  constructor
                  · rfl
                  · constructor
                    · funext current
                      by_cases h : current = address
                      · subst current
                        simp [updateLoopMemory, updateMemory]
                      · have h' : address ≠ current := Ne.symm h
                        simp [loopStateOfCrepState, updateLoopMemory, updateMemory,
                          h, h']
                    · intro name hname
                      have htemp : name ≠ context.maxVar + 1 := by omega
                      simp [loopStateOfCrepState, updateLoopLocal, htemp]

theorem crepToLoopProgramCorrect_store32_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : α) :
    CrepToLoopProgramCorrect (.store32 (.const address) (.const value) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
            evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithCallsAndFfi, evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                        updateLoopLocal] at hloop
                      cases hloop
                      simp only [crepToLoopControlRel, crepToLoopStateRel]
                      constructor
                      · rfl
                      · constructor
                        · funext current
                          by_cases h : current = address
                          · subst current
                            simp [updateLoopMemory, updateMemory]
                          · have h' : address ≠ current := Ne.symm h
                            simp [loopStateOfCrepState, updateLoopMemory, updateMemory,
                              h, h']
                        · intro name hname
                          have htemp : name ≠ context.maxVar + 1 := by omega
                          have htemp' : name ≠ context.maxVar + 2 := by omega
                          simp [loopStateOfCrepState, updateLoopLocal, htemp, htemp']
                  | succ targetFuel =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                        updateLoopLocal] at hloop
                      cases hloop
                      simp only [crepToLoopControlRel, crepToLoopStateRel]
                      constructor
                      · rfl
                      · constructor
                        · funext current
                          by_cases h : current = address
                          · subst current
                            simp [updateLoopMemory, updateMemory]
                          · have h' : address ≠ current := Ne.symm h
                            simp [loopStateOfCrepState, updateLoopMemory, updateMemory,
                              h, h']
                        · intro name hname
                          have htemp : name ≠ context.maxVar + 1 := by omega
                          have htemp' : name ≠ context.maxVar + 2 := by omega
                          simp [loopStateOfCrepState, updateLoopLocal, htemp, htemp']

theorem crepToLoopProgramCorrect_storeByte_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : α) :
    CrepToLoopProgramCorrect (.storeByte (.const address) (.const value) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
            evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithCallsAndFfi, evalLoopProg] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp] at hloop
              | succ targetFuel =>
                  cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                    updateLoopLocal] at hloop
                  cases hloop
                  simp only [crepToLoopControlRel, crepToLoopStateRel]
                  constructor
                  · rfl
                  · constructor
                    · funext current
                      by_cases h : current = address
                      · subst current
                        simp [updateLoopMemory, updateMemory]
                      · have h' : address ≠ current := Ne.symm h
                        simp [loopStateOfCrepState, updateLoopMemory, updateMemory,
                          h, h']
                    · intro name hname
                      have htemp : name ≠ context.maxVar + 1 := by omega
                      have htemp' : name ≠ context.maxVar + 2 := by omega
                      simp [loopStateOfCrepState, updateLoopLocal, htemp, htemp']
              | succ targetFuel =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                        updateLoopLocal] at hloop
                      cases hloop
                      simp only [crepToLoopControlRel, crepToLoopStateRel]
                      constructor
                      · rfl
                      · constructor
                        · funext current
                          by_cases h : current = address
                          · subst current
                            simp [updateLoopMemory, updateMemory]
                          · have h' : address ≠ current := Ne.symm h
                            simp [loopStateOfCrepState, updateLoopMemory, updateMemory,
                              h, h']
                        · intro name hname
                          have htemp : name ≠ context.maxVar + 1 := by omega
                          have htemp' : name ≠ context.maxVar + 2 := by omega
                          simp [loopStateOfCrepState, updateLoopLocal, htemp, htemp']

theorem crepToLoopProgramCorrect_assign_load32_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : Nat) (address : α) :
    CrepToLoopProgramCorrect
      (.assign name (.load32 (.const address)) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hmemory : state.memory address with
  | none => simp [hmemory] at hcrep
  | some value =>
      simp [hmemory] at hcrep
      subst crepResult
      cases targetFuel with
      | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithCallsAndFfi, evalLoopProg] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp] at hloop
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                            updateLoopLocal, loopStateOfCrepState, hmemory] at hloop
                          cases hloop
                          simp only [crepToLoopControlRel, crepToLoopStateRel]
                          constructor
                          · simp
                          · constructor
                            · simp
                            · intro current hcurrent
                              have htemp : current ≠ context.maxVar + 1 := by omega
                              simp [updateCrepLocal, updateLoopLocal, htemp]
                      | succ targetFuel =>
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                            updateLoopLocal, loopStateOfCrepState, hmemory] at hloop
                          cases hloop
                          simp only [crepToLoopControlRel, crepToLoopStateRel]
                          constructor
                          · simp
                          · constructor
                            · simp
                            · intro current hcurrent
                              have htemp : current ≠ context.maxVar + 1 := by omega
                              simp [updateCrepLocal, updateLoopLocal, htemp]

theorem crepToLoopProgramCorrect_assign_loadByte_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : Nat) (address : α) :
    CrepToLoopProgramCorrect
      (.assign name (.loadByte (.const address)) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp] at hcrep
  cases hmemory : state.memory address with
  | none => simp [hmemory] at hcrep
  | some value =>
      simp [hmemory] at hcrep
      subst crepResult
      cases targetFuel with
      | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          cases targetFuel with
          | zero =>
              simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                evalLoopProgWithCallsAndFfi] at hloop
          | succ targetFuel =>
              cases targetFuel with
              | zero =>
                  simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                    evalLoopProgWithCallsAndFfi, evalLoopProg] at hloop
              | succ targetFuel =>
                  cases targetFuel with
                  | zero =>
                      simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                        evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp] at hloop
                  | succ targetFuel =>
                      cases targetFuel with
                      | zero =>
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                            updateLoopLocal, loopStateOfCrepState, hmemory] at hloop
                          cases hloop
                          simp only [crepToLoopControlRel, crepToLoopStateRel]
                          constructor
                          · simp
                          · constructor
                            · simp
                            · intro current hcurrent
                              have htemp : current ≠ context.maxVar + 1 := by omega
                              simp [updateCrepLocal, updateLoopLocal, htemp]
                      | succ targetFuel =>
                          simp [loopCompileProg, loopCompileExp, loopNestedSeq,
                            evalLoopProgWithCallsAndFfi, evalLoopProg, evalLoopExp,
                            updateLoopLocal, loopStateOfCrepState, hmemory] at hloop
                          cases hloop
                          simp only [crepToLoopControlRel, crepToLoopStateRel]
                          constructor
                          · simp
                          · constructor
                            · simp
                            · intro current hcurrent
                              have htemp : current ≠ context.maxVar + 1 := by omega
                              simp [updateCrepLocal, updateLoopLocal, htemp]

theorem crepToLoopProgramCorrect_assign_add_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : Nat) (left right : α) :
    CrepToLoopProgramCorrect
      (.assign name (.op .add [.const left, .const right]) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp, evalPanBinOp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp,
            evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          simp [loopCompileProg, loopCompileExp,
            loopCompileExp.loopCompileExps,
            loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg,
            evalLoopExp] at hloop
          cases hloop
          simp [crepToLoopControlRel, crepToLoopStateRel,
            loopStateOfCrepState, updateCrepLocal, updateLoopLocal,
            evalLoopBinOp]

theorem crepToLoopProgramCorrect_assign_sub_const
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (name : Nat) (left right : α) :
    CrepToLoopProgramCorrect
      (.assign name (.op .sub [.const left, .const right]) : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg, evalCrepFullExp, evalPanBinOp] at hcrep
  subst crepResult
  cases targetFuel with
  | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
  | succ targetFuel =>
      cases targetFuel with
      | zero =>
          simp [loopCompileProg, loopCompileExp,
            evalLoopProgWithCallsAndFfi] at hloop
      | succ targetFuel =>
          simp [loopCompileProg, loopCompileExp,
            loopCompileExp.loopCompileExps,
            loopNestedSeq, evalLoopProgWithCallsAndFfi, evalLoopProg,
            evalLoopExp, evalLoopBinOp] at hloop
          cases hloop
          simp [crepToLoopControlRel, crepToLoopStateRel,
            loopStateOfCrepState, updateCrepLocal, updateLoopLocal]

theorem crepToLoopProgramCorrect_extCall
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    CrepToLoopProgramCorrect
      (.extCall function configuration configurationLength array arrayLength : CrepProg α) := by
  intro context functions crepFunctions primitive ffi sharedMem
    baseAddress topAddress sourceFuel targetFuel state live crepResult loopResult
    hcrep hloop
  simp [evalCrepFullProg] at hcrep
  cases hc : state.locals configuration with
  | none => simp [hc] at hcrep
  | some configurationValue =>
      cases hcl : state.locals configurationLength with
      | none => simp [hc, hcl] at hcrep
      | some configurationLengthValue =>
          cases ha : state.locals array with
          | none => simp [hc, hcl, ha] at hcrep
          | some arrayValue =>
              cases hal : state.locals arrayLength with
              | none => simp [hc, hcl, ha, hal] at hcrep
              | some arrayLengthValue =>
                  cases hffi : ffi function configurationValue configurationLengthValue
                      arrayValue arrayLengthValue state with
                  | none => simp [hc, hcl, ha, hal, hffi] at hcrep
                  | some ffiResult =>
                      cases ffiResult with
                      | returned state' =>
                          simp [hc, hcl, ha, hal, hffi] at hcrep
                          subst crepResult
                          have hffi' :
                              ffi function configurationValue configurationLengthValue
                                arrayValue arrayLengthValue
                                ({ locals := state.locals, memory := state.memory,
                                   globals := state.globals } : CrepState α) =
                                some (.returned state') := by
                            simpa using hffi
                          cases targetFuel with
                          | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
                          | succ targetFuel =>
                              simp [loopCompileProg] at hloop
                              rw [evalLoopProgWithCallsAndFfi_ffi] at hloop
                              simp [loopFfiOfCrepFfi, crepStateOfLoopState,
                                loopStateOfCrepState, hc, hcl, ha, hal, hffi'] at hloop
                              cases hloop
                              simp [crepToLoopControlRel, crepToLoopStateRel]
                      | final event =>
                          simp [hc, hcl, ha, hal, hffi] at hcrep
                          have hffi' :
                              ffi function configurationValue configurationLengthValue
                                arrayValue arrayLengthValue
                                ({ locals := state.locals, memory := state.memory,
                                   globals := state.globals } : CrepState α) =
                                some (.final event) := by
                            simpa using hffi
                          cases targetFuel with
                          | zero => simp [evalLoopProgWithCallsAndFfi] at hloop
                          | succ targetFuel =>
                              simp [loopCompileProg] at hloop
                              rw [evalLoopProgWithCallsAndFfi_ffi] at hloop
                              simp [loopFfiOfCrepFfi, crepStateOfLoopState,
                                loopStateOfCrepState, hc, hcl, ha, hal, hffi'] at hloop

theorem crepToLoopProgramCorrect_induction
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (hskip : CrepToLoopProgramCorrect (.skip : CrepProg α))
    (hdec : ∀ (name : Nat) (value : CrepExp α) (body : CrepProg α),
      CrepToLoopProgramCorrect body →
      CrepToLoopProgramCorrect (.dec name value body))
    (hassign : ∀ (name : Nat) (value : CrepExp α),
      CrepToLoopProgramCorrect (.assign name value))
    (hprimitive : ∀ (names : List Nat) (operator : PrimOp)
      (arguments : List Nat),
      CrepToLoopProgramCorrect
        (@CrepProg.primitive α names operator arguments))
    (hstore : ∀ (address value : CrepExp α),
      CrepToLoopProgramCorrect (.store address value))
    (hstore32 : ∀ (address value : CrepExp α),
      CrepToLoopProgramCorrect (.store32 address value))
    (hstoreByte : ∀ (address value : CrepExp α),
      CrepToLoopProgramCorrect (.storeByte address value))
    (hstoreGlob : ∀ (address : α) (value : CrepExp α),
      CrepToLoopProgramCorrect (.storeGlob address value))
    (hseq : ∀ (first second : CrepProg α),
      CrepToLoopProgramCorrect first →
      CrepToLoopProgramCorrect second →
      CrepToLoopProgramCorrect (.seq first second))
    (hite : ∀ (condition : CrepExp α) (thenBranch elseBranch : CrepProg α),
      CrepToLoopProgramCorrect thenBranch →
      CrepToLoopProgramCorrect elseBranch →
      CrepToLoopProgramCorrect (.ite condition thenBranch elseBranch))
    (hwhile : ∀ (condition : CrepExp α) (body : CrepProg α),
      CrepToLoopProgramCorrect body →
      CrepToLoopProgramCorrect (.while condition body))
    (hbreak : ∀ (label : Nat),
      CrepToLoopProgramCorrect (@CrepProg.break α label))
    (hcontinue : ∀ (label : Nat),
      CrepToLoopProgramCorrect (@CrepProg.continue α label))
    (hcall : ∀
      (returnInfo : Option (List Nat × Option (α × CrepProg α)))
      (name : FunName) (arguments : List (CrepExp α)),
      (match returnInfo with
       | some (_, some (_, handler)) => CrepToLoopProgramCorrect handler
       | _ => True) →
      CrepToLoopProgramCorrect (.call returnInfo name arguments))
    (hextCall : ∀ (function : FunName)
      (configuration configurationLength array arrayLength : Nat),
      CrepToLoopProgramCorrect
        (@CrepProg.extCall α function configuration configurationLength array
          arrayLength))
    (hraise : ∀ (exception : α),
      CrepToLoopProgramCorrect (.raise exception))
    (hreturn : ∀ (values : List (CrepExp α)),
      CrepToLoopProgramCorrect (.return values))
    (hshMem : ∀ (operator : CrepMemOp) (name : Nat) (address : CrepExp α),
      CrepToLoopProgramCorrect (.shMem operator name address))
    (htick : CrepToLoopProgramCorrect (.tick : CrepProg α)) :
    ∀ program : CrepProg α, CrepToLoopProgramCorrect program := by
  let rec go : (program : CrepProg α) → CrepToLoopProgramCorrect program
    | .skip => hskip
    | .dec name value body => hdec name value body (go body)
    | .assign name value => hassign name value
    | .primitive names operator arguments =>
        hprimitive names operator arguments
    | .store address value => hstore address value
    | .store32 address value => hstore32 address value
    | .storeByte address value => hstoreByte address value
    | .storeGlob address value => hstoreGlob address value
    | .seq first second => hseq first second (go first) (go second)
    | .ite condition thenBranch elseBranch =>
        hite condition thenBranch elseBranch (go thenBranch) (go elseBranch)
    | .while condition body => hwhile condition body (go body)
    | .break label => hbreak label
    | .continue label => hcontinue label
    | .call returnInfo name arguments =>
        hcall returnInfo name arguments (by
          cases returnInfo with
          | none => exact True.intro
          | some info =>
              cases info with
              | mk destinations handlerInfo =>
                  cases handlerInfo with
                  | none => exact True.intro
                  | some handler =>
                      cases handler with
                      | mk exception handlerProgram =>
                          exact go handlerProgram)
    | .extCall function configuration configurationLength array arrayLength =>
        hextCall function configuration configurationLength array arrayLength
    | .raise exception => hraise exception
    | .return values => hreturn values
    | .shMem operator name address => hshMem operator name address
    | .tick => htick
    termination_by program => sizeOf program
  exact fun program => go program

theorem crepToLoopProgramCorrectWithPrimitive_induction
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α] [Div α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (hskip : CrepToLoopProgramCorrectWithPrimitive (.skip : CrepProg α))
    (hdec : ∀ (name : Nat) (value : CrepExp α) (body : CrepProg α),
      CrepToLoopProgramCorrectWithPrimitive body →
      CrepToLoopProgramCorrectWithPrimitive (.dec name value body))
    (hassign : ∀ (name : Nat) (value : CrepExp α),
      CrepToLoopProgramCorrectWithPrimitive (.assign name value))
    (hprimitive : ∀ (names : List Nat) (operator : PrimOp)
      (arguments : List Nat),
      CrepToLoopProgramCorrectWithPrimitive
        (@CrepProg.primitive α names operator arguments))
    (hstore : ∀ (address value : CrepExp α),
      CrepToLoopProgramCorrectWithPrimitive (.store address value))
    (hstore32 : ∀ (address value : CrepExp α),
      CrepToLoopProgramCorrectWithPrimitive (.store32 address value))
    (hstoreByte : ∀ (address value : CrepExp α),
      CrepToLoopProgramCorrectWithPrimitive (.storeByte address value))
    (hstoreGlob : ∀ (address : α) (value : CrepExp α),
      CrepToLoopProgramCorrectWithPrimitive (.storeGlob address value))
    (hseq : ∀ (first second : CrepProg α),
      CrepToLoopProgramCorrectWithPrimitive first →
      CrepToLoopProgramCorrectWithPrimitive second →
      CrepToLoopProgramCorrectWithPrimitive (.seq first second))
    (hite : ∀ (condition : CrepExp α) (thenBranch elseBranch : CrepProg α),
      CrepToLoopProgramCorrectWithPrimitive thenBranch →
      CrepToLoopProgramCorrectWithPrimitive elseBranch →
      CrepToLoopProgramCorrectWithPrimitive
        (.ite condition thenBranch elseBranch))
    (hwhile : ∀ (condition : CrepExp α) (body : CrepProg α),
      CrepToLoopProgramCorrectWithPrimitive body →
      CrepToLoopProgramCorrectWithPrimitive (.while condition body))
    (hbreak : ∀ (label : Nat),
      CrepToLoopProgramCorrectWithPrimitive (@CrepProg.break α label))
    (hcontinue : ∀ (label : Nat),
      CrepToLoopProgramCorrectWithPrimitive (@CrepProg.continue α label))
    (hcall : ∀
      (returnInfo : Option (List Nat × Option (α × CrepProg α)))
      (name : FunName) (arguments : List (CrepExp α)),
      (match returnInfo with
       | some (_, some (_, handler)) =>
           CrepToLoopProgramCorrectWithPrimitive handler
       | _ => True) →
      CrepToLoopProgramCorrectWithPrimitive
        (.call returnInfo name arguments))
    (hextCall : ∀ (function : FunName)
      (configuration configurationLength array arrayLength : Nat),
      CrepToLoopProgramCorrectWithPrimitive
        (@CrepProg.extCall α function configuration configurationLength array
          arrayLength))
    (hraise : ∀ (exception : α),
      CrepToLoopProgramCorrectWithPrimitive (.raise exception))
    (hreturn : ∀ (values : List (CrepExp α)),
      CrepToLoopProgramCorrectWithPrimitive (.return values))
    (hshMem : ∀ (operator : CrepMemOp) (name : Nat) (address : CrepExp α),
      CrepToLoopProgramCorrectWithPrimitive (.shMem operator name address))
    (htick : CrepToLoopProgramCorrectWithPrimitive (.tick : CrepProg α)) :
    ∀ program : CrepProg α,
      CrepToLoopProgramCorrectWithPrimitive program := by
  let rec go : (program : CrepProg α) →
      CrepToLoopProgramCorrectWithPrimitive program
    | .skip => hskip
    | .dec name value body => hdec name value body (go body)
    | .assign name value => hassign name value
    | .primitive names operator arguments =>
        hprimitive names operator arguments
    | .store address value => hstore address value
    | .store32 address value => hstore32 address value
    | .storeByte address value => hstoreByte address value
    | .storeGlob address value => hstoreGlob address value
    | .seq first second => hseq first second (go first) (go second)
    | .ite condition thenBranch elseBranch =>
        hite condition thenBranch elseBranch (go thenBranch) (go elseBranch)
    | .while condition body => hwhile condition body (go body)
    | .break label => hbreak label
    | .continue label => hcontinue label
    | .call returnInfo name arguments =>
        hcall returnInfo name arguments (by
          cases returnInfo with
          | none => exact True.intro
          | some info =>
              cases info with
              | mk destinations handlerInfo =>
                  cases handlerInfo with
                  | none => exact True.intro
                  | some handler =>
                      cases handler with
                      | mk exception handlerProgram =>
                          exact go handlerProgram)
    | .extCall function configuration configurationLength array arrayLength =>
        hextCall function configuration configurationLength array arrayLength
    | .raise exception => hraise exception
    | .return values => hreturn values
    | .shMem operator name address => hshMem operator name address
    | .tick => htick
    termination_by program => sizeOf program
  exact fun program => go program

end Flapjack
