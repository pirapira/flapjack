import Flapjack.CrepeAssignmentSequenceCorrectness
import Flapjack.CrepeDeclarationRelation
import Flapjack.CrepeNestedDecsStability

/-!
Reusable evaluator facts for the temporary path of flattened assignments.
Fresh declarations first bind the compiled values, after which the compiler
assigns the destination slots from fresh variables and restores those
variables on exit.
-/

namespace Flapjack

theorem evalCrepFullExps_varList_updateCrepLocalList
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (locals : Nat → Option α) (memory : α → Option α)
    (baseAddress topAddress : α)
    (names : List Nat) (values : List α)
    (hlength : names.length = values.length)
    (hdistinct : CrepDistinctNames names) :
    evalCrepFullExps
        (updateCrepLocalList locals names values) memory
        baseAddress topAddress (names.map (fun name => .var name)) =
      some values := by
  have hread := readCrepLocals_updateCrepLocalList locals names values
    hlength hdistinct
  have hvars : ∀ (current : Nat → Option α) (currentNames : List Nat),
      evalCrepFullExps current memory baseAddress topAddress
          (currentNames.map (fun name => .var name)) =
        readCrepLocals current currentNames := by
    intro current currentNames
    induction currentNames with
    | nil => simp [evalCrepFullExps, readCrepLocals]
    | cons name currentNames ih =>
        simp only [List.map_cons, evalCrepFullExps, evalCrepFullExp,
          readCrepLocals]
        rw [ih]
  rw [hvars]
  exact hread

theorem evalCrepFullProg_nestedDecs_assignList
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat) (state : CrepState α)
    (names : List Nat) (expressions : List (CrepExp α)) (body : CrepProg α)
    (values : List α) (result : CrepControlResult α)
    (hlength : names.length = expressions.length)
    (hdistinct : CrepDistinctNames names)
    (hnot : ∀ name ∈ names, ∀ expression ∈ expressions,
      name ∉ crepExpVars expression)
    (heval : evalCrepFullExps state.locals state.memory
      baseAddress topAddress expressions = some values)
    (hbody : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { state with locals := updateCrepLocalList state.locals names values } body =
      some result) :
    evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress (fuel + names.length) state
      (nestedDecs names expressions body) =
      some (restoreCrepResultList state.locals names result) := by
  have hnested := crepNestedDecsEval_of_evalExps_stable functions primitive ffi sharedMem
    baseAddress topAddress fuel state names expressions body result values
    hlength hnot heval hbody
  exact evalCrepFullProg_nestedDecs_of_eval functions primitive ffi sharedMem
    baseAddress topAddress fuel state names expressions body result hdistinct hnested

end Flapjack
