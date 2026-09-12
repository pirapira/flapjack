import Flapjack.CrepeCallSequenceInversion

/-!
Inversion for a successful compiled declaration call.

The compiler expands `decCall` into zero-valued declarations around a call
and its continuation.  This theorem removes that expansion from a successful
evaluation and exposes the exact callee/continuation witnesses needed by the
source-to-Crep correctness induction.
-/

namespace Flapjack

theorem evalCrepFullProg_decCall_inversion
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (targetFuel : Nat)
    (state : CrepState α) (name : VarName) (shape : Shape)
    (function : FunName) (arguments : List (Exp α)) (body : Prog α)
    (compiledArguments : List (CrepExp α)) (result : CrepControlResult α)
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (heval : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (compileProg context (.decCall name shape function arguments body)) =
      some result) :
    ∃ fuel callResult,
      targetFuel = (fuel + 2) + (allocatedNames context shape).length ∧
      evalCrepFullCall functions primitive ffi sharedMem
        baseAddress topAddress fuel
        { state with
            locals := initializeCrepLocals state.locals
              (allocatedNames context shape) }
        (some (allocatedNames context shape, none)) function compiledArguments =
        some callResult ∧
      match callResult with
      | .normal callState =>
          ∃ bodyResult,
            evalCrepFullProg functions primitive ffi sharedMem
              baseAddress topAddress (fuel + 1) callState
              (compileProg
                { context with
                    vars := (name, (shape, allocatedNames context shape)) ::
                      context.vars
                    maxVar := context.maxVar + Shape.shapeSize shape }
                body) = some bodyResult ∧
            restoreCrepResultList state.locals
              (allocatedNames context shape) bodyResult = result
      | other =>
          restoreCrepResultList state.locals
            (allocatedNames context shape) other = result := by
  have hcompileProg :
      compileProg context (.decCall name shape function arguments body) =
        nestedDecs (allocatedNames context shape)
          ((allocatedNames context shape).map
            (fun _ => CrepExp.const (0 : α)))
          (.seq
            (.call (some (allocatedNames context shape, none)) function
              compiledArguments)
            (compileProg
              { context with
                  vars := (name, (shape, allocatedNames context shape)) ::
                    context.vars
                  maxVar := context.maxVar + Shape.shapeSize shape }
              body)) := by
    simp [compileProg, hcompileArgs]
  rw [hcompileProg] at heval
  have happend : ∀ (entries : List Nat) (value : Nat),
      CrepDistinctNames entries → value ∉ entries →
      CrepDistinctNames (entries ++ [value]) := by
    intro entries value
    induction entries generalizing value with
    | nil =>
        intro _ _
        simp [CrepDistinctNames]
    | cons head tail ih =>
        intro hdistinct hnot
        rcases hdistinct with ⟨hhead, htail⟩
        have hheadValue : head ≠ value := by
          intro heq
          apply hnot
          simp [heq]
        have htailNot : value ∉ tail := by
          intro hmem
          apply hnot
          simp [hmem]
        have hheadNot : head ∉ tail ++ [value] := by
          intro hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | hmem
          · exact hhead hmem
          · exact hheadValue hmem
        exact ⟨hheadNot, ih value htail htailNot⟩
  have hdistinctRange : ∀ (start count : Nat),
      CrepDistinctNames ((List.range count).map (fun offset => start + offset)) := by
    intro start count
    induction count with
    | zero =>
        simp [CrepDistinctNames]
    | succ count ih =>
        have hnot : start + count ∉
            (List.range count).map (fun offset => start + offset) := by
          intro hmem
          obtain ⟨offset, hoff, heq⟩ := List.mem_map.mp hmem
          have hofflt : offset < count := List.mem_range.mp hoff
          omega
        simpa [List.range_succ, List.map_append] using
          happend ((List.range count).map (fun offset => start + offset))
            (start + count) ih hnot
  have hdistinct : CrepDistinctNames (allocatedNames context shape) := by
    simpa [allocatedNames] using
      hdistinctRange (context.maxVar + 1) (Shape.shapeSize shape)
  have hlength :
      (allocatedNames context shape).length =
        ((allocatedNames context shape).map
          (fun _ => CrepExp.const (0 : α))).length := by
    simp
  obtain ⟨nestedFuel, innerResult, htargetFuel, hnested, hrestore⟩ :=
    crepNestedDecsEval_of_eval functions primitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (allocatedNames context shape)
      ((allocatedNames context shape).map
        (fun _ => CrepExp.const (0 : α)))
      (.seq
        (.call (some (allocatedNames context shape, none)) function
          compiledArguments)
        (compileProg
          { context with
              vars := (name, (shape, allocatedNames context shape)) ::
                context.vars
              maxVar := context.maxVar + Shape.shapeSize shape }
          body))
      result hdistinct hlength heval
  have hseq := crepNestedDecsEval_const_zero_inv
    functions primitive ffi sharedMem baseAddress topAddress nestedFuel state
    (allocatedNames context shape)
    (.seq
      (.call (some (allocatedNames context shape, none)) function
        compiledArguments)
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) ::
              context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body)) innerResult hnested
  cases nestedFuel with
  | zero =>
      simp [evalCrepFullProg] at hseq
  | succ nestedFuel =>
      cases nestedFuel with
      | zero =>
          simp [evalCrepFullProg] at hseq
      | succ fuel =>
          have hinv := evalCrepFullProg_call_seq_inversion
            functions primitive ffi sharedMem baseAddress topAddress fuel
            { state with
                locals := initializeCrepLocals state.locals
                  (allocatedNames context shape) }
            (some (allocatedNames context shape, none)) function
            compiledArguments
            (compileProg
              { context with
                  vars := (name, (shape, allocatedNames context shape)) ::
                    context.vars
                  maxVar := context.maxVar + Shape.shapeSize shape }
              body) innerResult hseq
          rcases hinv with ⟨callResult, hcall, hcontinuation⟩
          refine ⟨fuel, callResult, ?_, hcall, ?_⟩
          · simp [htargetFuel, Nat.add_comm, Nat.add_left_comm]
          · cases callResult with
            | normal callState =>
                exact ⟨innerResult, hcontinuation, hrestore⟩
            | returned callState values
            | raised callState exception
            | broke callState label
            | continued callState label
            | finalFfi callState event =>
                simpa [hcontinuation] using hrestore

theorem evalCrepFullProgState_decCall_inversion
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : CompileContext α) (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (targetFuel : Nat)
    (state : CrepState α) (name : VarName) (shape : Shape)
    (function : FunName) (arguments : List (Exp α)) (body : Prog α)
    (compiledArguments : List (CrepExp α)) (result : CrepControlResult α)
    (hcompileArgs : compileArgs context arguments = compiledArguments)
    (heval : evalCrepFullProgState functions primitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (compileProg context (.decCall name shape function arguments body)) =
      some result) :
    ∃ fuel callResult,
      targetFuel = (fuel + 2) + (allocatedNames context shape).length ∧
      evalCrepFullCallState functions primitive ffi sharedMem
        baseAddress topAddress fuel
        { state with
            locals := initializeCrepLocals state.locals
              (allocatedNames context shape) }
        (some (allocatedNames context shape, none)) function compiledArguments =
        some callResult ∧
      match callResult with
      | .normal callState =>
          ∃ bodyResult,
            evalCrepFullProgState functions primitive ffi sharedMem
              baseAddress topAddress (fuel + 1) callState
              (compileProg
                { context with
                    vars := (name, (shape, allocatedNames context shape)) ::
                      context.vars
                    maxVar := context.maxVar + Shape.shapeSize shape }
                body) = some bodyResult ∧
            restoreCrepResultList state.locals
              (allocatedNames context shape) bodyResult = result
      | other =>
          restoreCrepResultList state.locals
            (allocatedNames context shape) other = result := by
  have hcompileProg :
      compileProg context (.decCall name shape function arguments body) =
        nestedDecs (allocatedNames context shape)
          ((allocatedNames context shape).map
            (fun _ => CrepExp.const (0 : α)))
          (.seq
            (.call (some (allocatedNames context shape, none)) function
              compiledArguments)
            (compileProg
              { context with
                  vars := (name, (shape, allocatedNames context shape)) ::
                    context.vars
                  maxVar := context.maxVar + Shape.shapeSize shape }
              body)) := by
    simp [compileProg, hcompileArgs]
  rw [hcompileProg] at heval
  have happend : ∀ (entries : List Nat) (value : Nat),
      CrepDistinctNames entries → value ∉ entries →
      CrepDistinctNames (entries ++ [value]) := by
    intro entries value
    induction entries generalizing value with
    | nil =>
        intro _ _
        simp [CrepDistinctNames]
    | cons head tail ih =>
        intro hdistinct hnot
        rcases hdistinct with ⟨hhead, htail⟩
        have hheadValue : head ≠ value := by
          intro heq
          apply hnot
          simp [heq]
        have htailNot : value ∉ tail := by
          intro hmem
          apply hnot
          simp [hmem]
        have hheadNot : head ∉ tail ++ [value] := by
          intro hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | hmem
          · exact hhead hmem
          · exact hheadValue hmem
        exact ⟨hheadNot, ih value htail htailNot⟩
  have hdistinctRange : ∀ (start count : Nat),
      CrepDistinctNames ((List.range count).map (fun offset => start + offset)) := by
    intro start count
    induction count with
    | zero =>
        simp [CrepDistinctNames]
    | succ count ih =>
        have hnot : start + count ∉
            (List.range count).map (fun offset => start + offset) := by
          intro hmem
          obtain ⟨offset, hoff, heq⟩ := List.mem_map.mp hmem
          have hofflt : offset < count := List.mem_range.mp hoff
          omega
        simpa [List.range_succ, List.map_append] using
          happend ((List.range count).map (fun offset => start + offset))
            (start + count) ih hnot
  have hdistinct : CrepDistinctNames (allocatedNames context shape) := by
    simpa [allocatedNames] using
      hdistinctRange (context.maxVar + 1) (Shape.shapeSize shape)
  have hlength :
      (allocatedNames context shape).length =
        ((allocatedNames context shape).map
          (fun _ => CrepExp.const (0 : α))).length := by
    simp
  obtain ⟨nestedFuel, innerResult, htargetFuel, hnested, hrestore⟩ :=
    crepNestedDecsStateEval_of_eval functions primitive ffi sharedMem
      baseAddress topAddress targetFuel state
      (allocatedNames context shape)
      ((allocatedNames context shape).map
        (fun _ => CrepExp.const (0 : α)))
      (.seq
        (.call (some (allocatedNames context shape, none)) function
          compiledArguments)
        (compileProg
          { context with
              vars := (name, (shape, allocatedNames context shape)) ::
                context.vars
              maxVar := context.maxVar + Shape.shapeSize shape }
          body))
      result hdistinct hlength heval
  have hseq := crepNestedDecsStateEval_const_zero_inv
    functions primitive ffi sharedMem baseAddress topAddress nestedFuel state
    (allocatedNames context shape)
    (.seq
      (.call (some (allocatedNames context shape, none)) function
        compiledArguments)
      (compileProg
        { context with
            vars := (name, (shape, allocatedNames context shape)) ::
              context.vars
            maxVar := context.maxVar + Shape.shapeSize shape }
        body)) innerResult hnested
  cases nestedFuel with
  | zero =>
      simp [evalCrepFullProgState] at hseq
  | succ nestedFuel =>
      cases nestedFuel with
      | zero =>
          simp [evalCrepFullProgState] at hseq
      | succ fuel =>
          have hinv := evalCrepFullProgState_call_seq_inversion
            functions primitive ffi sharedMem baseAddress topAddress fuel
            { state with
                locals := initializeCrepLocals state.locals
                  (allocatedNames context shape) }
            (some (allocatedNames context shape, none)) function
            compiledArguments
            (compileProg
              { context with
                  vars := (name, (shape, allocatedNames context shape)) ::
                    context.vars
                  maxVar := context.maxVar + Shape.shapeSize shape }
              body) innerResult hseq
          rcases hinv with ⟨callResult, hcall, hcontinuation⟩
          refine ⟨fuel, callResult, ?_, hcall, ?_⟩
          · simp [htargetFuel, Nat.add_comm, Nat.add_left_comm]
          · cases callResult with
            | normal callState =>
                exact ⟨innerResult, hcontinuation, hrestore⟩
            | returned callState values
            | raised callState exception
            | broke callState label
            | continued callState label
            | finalFfi callState event =>
                simpa [hcontinuation] using hrestore

end Flapjack
