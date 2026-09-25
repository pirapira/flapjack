import Flapjack.Pancake.Semantics.PanSem.Total
import Flapjack.PanShMemStore
import Flapjack.Pancake.Semantics.LoopSem

/-!
# HOL-shaped total statement-clause assembly steps

Interface glue for the total HOL-shaped `panSem$evaluate` fragment
(`cakeml/pancake/semantics/panSemScript.sml:556-736`).  Every expression-bearing
constructor of HOL `evaluate` first evaluates a source expression with `eval` and
then either continues with the value or returns `SOME Error` with the state
unchanged.  This module packages that shared pattern once, over the complete
production `PanSemState`, and instantiates it for the `Assign`, `Return`, and
`Raise` clauses.  Everything here is untagged: it is assembly support for a
future exact `evaluate_def` port, not the port itself, and it uses the RV64
production word carrier.

The expression evaluation reuses `evalPanSemStateExp`, whose executed-path
agreement with the untagged `evalHOL` reference evaluator is established in
`Flapjack/Pancake/Semantics/PanSemStateEval.lean`.
-/

namespace Flapjack

/-- Shared expression-evaluation glue: evaluate a source `Exp` from the complete
    state; on a produced value hand it to the continuation, and on a failed
    evaluation return `SOME Error` with the state unchanged (HOL's
    `case eval s e of SOME v => ... | NONE => (SOME Error, s)` pattern). -/
def panSemTotalExprStep [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (expression : Exp (RiscV.Word 64))
    (onValue : PanValue (RiscV.Word 64) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  match evalPanSemStateExp state expression with
  | some value => onValue value
  | none => (some .error, state)

@[simp] theorem panSemTotalExprStep_some [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (expression : Exp (RiscV.Word 64)) (value : PanValue (RiscV.Word 64))
    (onValue : PanValue (RiscV.Word 64) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ))
    (heval : evalPanSemStateExp state expression = some value) :
    panSemTotalExprStep state expression onValue = onValue value := by
  simp [panSemTotalExprStep, heval]

theorem panSemTotalExprStep_none [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (expression : Exp (RiscV.Word 64))
    (onValue : PanValue (RiscV.Word 64) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ))
    (heval : evalPanSemStateExp state expression = none) :
    panSemTotalExprStep state expression onValue = (some .error, state) := by
  simp [panSemTotalExprStep, heval]

/-- HOL `Assign` (`panSemScript.sml:566-572`): evaluate the source, require
    `is_valid_value`, write through `set_kvar`, and return `SOME Error` with the
    state unchanged when the source fails or the destination is invalid.  A
    successful assignment is HOL's normal completion (`NONE`). -/
def panSemTotalAssignClause [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (kind : VarKind) (name : VarName) (expression : Exp (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprStep state expression (fun value =>
    if panValueAssignmentValid state.structs state.locals state.globals kind name value then
      (none,
        match kind with
        | .local => { state with locals := updatePanValueMap state.locals name value }
        | .global => { state with globals := updatePanValueMap state.globals name value })
    else
      (some .error, state))

@[simp] theorem panSemTotalAssignClause_none [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (kind : VarKind) (name : VarName) (expression : Exp (RiscV.Word 64))
    (heval : evalPanSemStateExp state expression = none) :
    panSemTotalAssignClause state kind name expression = (some .error, state) := by
  simp [panSemTotalAssignClause, panSemTotalExprStep, heval]

theorem panSemTotalAssignClause_normal [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (kind : VarKind) (name : VarName) (expression : Exp (RiscV.Word 64))
    (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExp state expression = some value)
    (hvalid : panValueAssignmentValid state.structs state.locals state.globals kind name value = true) :
    panSemTotalAssignClause state kind name expression =
      (none,
        match kind with
        | .local => { state with locals := updatePanValueMap state.locals name value }
        | .global => { state with globals := updatePanValueMap state.globals name value }) := by
  cases kind <;> simp [panSemTotalAssignClause, panSemTotalExprStep, heval, hvalid]

theorem panSemTotalAssignClause_invalid [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (kind : VarKind) (name : VarName) (expression : Exp (RiscV.Word 64))
    (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExp state expression = some value)
    (hvalid : panValueAssignmentValid state.structs state.locals state.globals kind name value = false) :
    panSemTotalAssignClause state kind name expression = (some .error, state) := by
  simp [panSemTotalAssignClause, panSemTotalExprStep, heval, hvalid]

/-- HOL `Return` (`panSemScript.sml:638-644`): evaluate the source, accept it
    only when `size_of_sh_with_ctxt structs (shape_of value) ≤ 32`, and clear
    locals on success. Failed evaluation or an oversized value returns
    `SOME Error` with the state unchanged. -/
def panSemTotalReturnClause [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (expression : Exp (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprStep state expression (fun value =>
    if sizeOfShWithCtxt state.structs.toHOL (panSemShapeOf value) ≤ 32 then
      (some (.returned value), panEmptyLocals state)
    else
      (some .error, state))

theorem panSemTotalReturnClause_some [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (expression : Exp (RiscV.Word 64)) (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExp state expression = some value) :
    sizeOfShWithCtxt state.structs.toHOL (panSemShapeOf value) ≤ 32 →
    panSemTotalReturnClause state expression =
      (some (.returned value), panEmptyLocals state) := by
  intro hsize
  simp [panSemTotalReturnClause, panSemTotalExprStep, heval, hsize]

theorem panSemTotalReturnClause_none [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (expression : Exp (RiscV.Word 64))
    (heval : evalPanSemStateExp state expression = none) :
    panSemTotalReturnClause state expression = (some .error, state) := by
  simp [panSemTotalReturnClause, panSemTotalExprStep, heval]

/-- HOL `Raise` (`panSemScript.sml:645-653`): require an exception shape for
    `eid`, evaluate the source, and accept only a value with that shape and at
    most 32 words. Success clears locals; every failed check returns
    `SOME Error` with the state unchanged. -/
def panSemTotalRaiseClause [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exceptionId : ExceptionId) (expression : Exp (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprStep state expression (fun value =>
    match state.exceptionShapes exceptionId with
    | some shape =>
        if panShapeMatches shape (panSemShapeOf value) &&
            sizeOfShWithCtxt state.structs.toHOL (panSemShapeOf value) ≤ 32 then
          (some (.exception exceptionId value), panEmptyLocals state)
        else
          (some .error, state)
    | none => (some .error, state))

theorem panSemTotalRaiseClause_some [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exceptionId : ExceptionId) (expression : Exp (RiscV.Word 64))
    (value : PanValue (RiscV.Word 64))
    (shape : Shape)
    (heval : evalPanSemStateExp state expression = some value)
    (hshape : state.exceptionShapes exceptionId = some shape)
    (hvalue : panShapeMatches shape (panSemShapeOf value) = true)
    (hsize : sizeOfShWithCtxt state.structs.toHOL (panSemShapeOf value) ≤ 32) :
    panSemTotalRaiseClause state exceptionId expression =
      (some (.exception exceptionId value), panEmptyLocals state) := by
  simp [panSemTotalRaiseClause, panSemTotalExprStep, heval, hshape, hvalue, hsize]

theorem panSemTotalRaiseClause_none [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exceptionId : ExceptionId) (expression : Exp (RiscV.Word 64))
    (heval : evalPanSemStateExp state expression = none) :
    panSemTotalRaiseClause state exceptionId expression = (some .error, state) := by
  simp [panSemTotalRaiseClause, panSemTotalExprStep, heval]

/-- Shared list-expression glue: evaluate a list of source expressions from the
    complete state; on produced values hand them to the continuation, and on a
    failed evaluation return `SOME Error` with the state unchanged (HOL's
    `case OPT_MMAP (eval s) es of SOME vs => ... | _ => (SOME Error, s)`
    pattern). -/
def panSemTotalExprListStep [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (expressions : List (Exp (RiscV.Word 64)))
    (onValues : List (PanValue (RiscV.Word 64)) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  match evalPanSemStateExps state expressions with
  | some values => onValues values
  | none => (some .error, state)

@[simp] theorem panSemTotalExprListStep_some [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (expressions : List (Exp (RiscV.Word 64)))
    (onValues : List (PanValue (RiscV.Word 64)) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ))
    (values : List (PanValue (RiscV.Word 64)))
    (heval : evalPanSemStateExps state expressions = some values) :
    panSemTotalExprListStep state expressions onValues = onValues values := by
  simp [panSemTotalExprListStep, heval]

theorem panSemTotalExprListStep_none [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (expressions : List (Exp (RiscV.Word 64)))
    (onValues : List (PanValue (RiscV.Word 64)) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ))
    (heval : evalPanSemStateExps state expressions = none) :
    panSemTotalExprListStep state expressions onValues = (some .error, state) := by
  simp [panSemTotalExprListStep, heval]

/-- HOL `Primitive` (`cakeml/pancake/semantics/panSemScript.sml:576`): evaluate
    the argument expressions, run the primitive handler, and, when the produced
    value is a valid new binding for the local name, install it; otherwise
    `SOME Error` with the state unchanged. -/
def panSemTotalPrimitiveClause [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (name : VarName) (operator : PrimOp)
    (arguments : List (Exp (RiscV.Word 64)))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprListStep state arguments (fun values =>
    match primitive operator values with
    | some value =>
        if panValueAssignmentValid state.structs state.locals state.globals
            .local name value then
          (none, { state with locals := updatePanValueMap state.locals name value })
        else (some .error, state)
    | none => (some .error, state))

theorem panSemTotalPrimitiveClause_none [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (name : VarName) (operator : PrimOp)
    (arguments : List (Exp (RiscV.Word 64)))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (heval : evalPanSemStateExps state arguments = none) :
    panSemTotalPrimitiveClause state name operator arguments primitive =
      (some .error, state) := by
  simp [panSemTotalPrimitiveClause, panSemTotalExprListStep, heval]

theorem panSemTotalPrimitiveClause_ok [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (name : VarName) (operator : PrimOp)
    (arguments : List (Exp (RiscV.Word 64)))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (values : List (PanValue (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExps state arguments = some values)
    (hprim : primitive operator values = some value)
    (hvalid : panValueAssignmentValid state.structs state.locals state.globals
      .local name value = true) :
    panSemTotalPrimitiveClause state name operator arguments primitive =
      (none, { state with locals := updatePanValueMap state.locals name value }) := by
  simp [panSemTotalPrimitiveClause, panSemTotalExprListStep, heval, hprim, hvalid]

theorem panSemTotalPrimitiveClause_invalid [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (name : VarName) (operator : PrimOp)
    (arguments : List (Exp (RiscV.Word 64)))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (values : List (PanValue (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExps state arguments = some values)
    (hprim : primitive operator values = some value)
    (hvalid : panValueAssignmentValid state.structs state.locals state.globals
      .local name value = false) :
    panSemTotalPrimitiveClause state name operator arguments primitive =
      (some .error, state) := by
  simp [panSemTotalPrimitiveClause, panSemTotalExprListStep, heval, hprim, hvalid]

theorem panSemTotalPrimitiveClause_primNone [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (name : VarName) (operator : PrimOp)
    (arguments : List (Exp (RiscV.Word 64)))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (values : List (PanValue (RiscV.Word 64)))
    (heval : evalPanSemStateExps state arguments = some values)
    (hprim : primitive operator values = none) :
    panSemTotalPrimitiveClause state name operator arguments primitive =
      (some .error, state) := by
  simp [panSemTotalPrimitiveClause, panSemTotalExprListStep, heval, hprim]

/-- HOL `Annot` (`cakeml/pancake/semantics/panSemScript.sml:641`): annotation is
    erased; normal completion with the state carried verbatim. -/
def panSemTotalAnnotClause {α : Type u} {σ : Type u}
    (state : PanSemState α (FfiState σ)) (_tag _text : String) :
    Option (PanSemHOLResult α) × PanSemState α (FfiState σ) :=
  (none, state)

@[simp] theorem panSemTotalAnnotClause_eq {α : Type u} {σ : Type u}
    (state : PanSemState α (FfiState σ)) (tag text : String) :
    panSemTotalAnnotClause state tag text = (none, state) := rfl

/-- HOL `Store` (`cakeml/pancake/semantics/panSemScript.sml:583-589`): evaluate
    the destination and the source; the destination must be a word; store the
    flattened source value at that address (`mem_stores addr (flatten value)
    s.memaddrs s.memory`), modelled here by `panValueStoreWithAccess` over the
    machine access.  Failed evaluation, a non-word destination, or a failed
    store all yield `SOME Error` with the state unchanged. -/
def panSemTotalStoreClause [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprStep state address (fun addressValue =>
    match addressValue with
    | .word addr =>
        panSemTotalExprStep state value (fun storedValue =>
          match panValueStoreWithAccess state.memory panSemBitVec64BytesInWord addr
              storedValue (some (panSemBitVec64MemoryAccess state)) with
          | some memory => (none, { state with memory := memory })
          | none => (some .error, state))
    | _ => (some .error, state))

@[simp] theorem panSemTotalStoreClause_none [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64))
    (heval : evalPanSemStateExp state address = none) :
    panSemTotalStoreClause state address value = (some .error, state) := by
  simp [panSemTotalStoreClause, panSemTotalExprStep, heval]

theorem panSemTotalStoreClause_ok [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) (addr : RiscV.Word 64)
    (storedValue : PanValue (RiscV.Word 64))
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (hevalAddr : evalPanSemStateExp state address = some (.word addr))
    (hevalValue : evalPanSemStateExp state value = some storedValue)
    (hstore : panValueStoreWithAccess state.memory panSemBitVec64BytesInWord addr
      storedValue (some (panSemBitVec64MemoryAccess state)) = some memory) :
    panSemTotalStoreClause state address value = (none, { state with memory := memory }) := by
  simp [panSemTotalStoreClause, panSemTotalExprStep, hevalAddr, hevalValue, hstore]

/-- HOL `Store32` (`cakeml/pancake/semantics/panSemScript.sml:590-596`): both the
    destination and the source must be words; store the low 32 bits widened back
    to the word carrier via `mem_store_32 s.memory s.memaddrs s.be adr (w2w w)`,
    modelled by the machine `access.store32`. -/
def panSemTotalStore32Clause [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprStep state address (fun addressValue =>
    match addressValue with
    | .word addr =>
        panSemTotalExprStep state value (fun storedValue =>
          match storedValue with
          | .word word =>
              match (panSemBitVec64MemoryAccess state).store32
                  (panSemBitVec64MemoryAccess state).domain state.memory
                  panSemBitVec64BytesInWord addr word with
              | some memory => (none, { state with memory := memory })
              | none => (some .error, state)
          | _ => (some .error, state))
    | _ => (some .error, state))

@[simp] theorem panSemTotalStore32Clause_none [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64))
    (heval : evalPanSemStateExp state address = none) :
    panSemTotalStore32Clause state address value = (some .error, state) := by
  simp [panSemTotalStore32Clause, panSemTotalExprStep, heval]

theorem panSemTotalStore32Clause_ok [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) (addr word : RiscV.Word 64)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (hevalAddr : evalPanSemStateExp state address = some (.word addr))
    (hevalValue : evalPanSemStateExp state value = some (.word word))
    (hstore : (panSemBitVec64MemoryAccess state).store32
      (panSemBitVec64MemoryAccess state).domain state.memory
      panSemBitVec64BytesInWord addr word = some memory) :
    panSemTotalStore32Clause state address value = (none, { state with memory := memory }) := by
  simp [panSemTotalStore32Clause, panSemTotalExprStep, hevalAddr, hevalValue, hstore]

/-- HOL `StoreByte` (`cakeml/pancake/semantics/panSemScript.sml:597-603`): both
    the destination and the source must be words; store the low byte via
    `mem_store_byte s.memory s.memaddrs s.be adr (w2w w)`, modelled by the
    machine `access.storeByte`. -/
def panSemTotalStoreByteClause [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprStep state address (fun addressValue =>
    match addressValue with
    | .word addr =>
        panSemTotalExprStep state value (fun storedValue =>
          match storedValue with
          | .word word =>
              match (panSemBitVec64MemoryAccess state).storeByte
                  (panSemBitVec64MemoryAccess state).domain state.memory
                  panSemBitVec64BytesInWord addr word with
              | some memory => (none, { state with memory := memory })
              | none => (some .error, state)
          | _ => (some .error, state))
    | _ => (some .error, state))

@[simp] theorem panSemTotalStoreByteClause_none [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64))
    (heval : evalPanSemStateExp state address = none) :
    panSemTotalStoreByteClause state address value = (some .error, state) := by
  simp [panSemTotalStoreByteClause, panSemTotalExprStep, heval]

theorem panSemTotalStoreByteClause_ok [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) (addr word : RiscV.Word 64)
    (memory : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (hevalAddr : evalPanSemStateExp state address = some (.word addr))
    (hevalValue : evalPanSemStateExp state value = some (.word word))
    (hstore : (panSemBitVec64MemoryAccess state).storeByte
      (panSemBitVec64MemoryAccess state).domain state.memory
      panSemBitVec64BytesInWord addr word = some memory) :
    panSemTotalStoreByteClause state address value = (none, { state with memory := memory }) := by
  simp [panSemTotalStoreByteClause, panSemTotalExprStep, hevalAddr, hevalValue, hstore]


-- HOL `Dec` statement clause (panSemScript.sml:556-561). Note `Dec` has no
-- `VarKind`: it always binds the name in `s.locals`.
def panSemTotalDecBind [BEq String] (state : PanSemState (RiscV.Word 64) (FfiState σ) )
    (name : VarName) (value : PanValue (RiscV.Word 64)) :
    PanSemState (RiscV.Word 64) (FfiState σ) :=
  { state with locals := updatePanValueMap state.locals name value }

/-- HOL `Dec` (`panSemScript.sml:556-561`): evaluate the source; on a value whose
    shape equals the declared shape, bind `name` in the locals, run the body,
    then restore the previous local binding of `name` with `res_var`. -/
def panSemTotalDecClause [BEq String] [LawfulBEq String] (state : PanSemState (RiscV.Word 64) (FfiState σ) )
    (name : VarName) (shape : Shape)
    (expression : Exp (RiscV.Word 64))
    (body : PanSemState (RiscV.Word 64) (FfiState σ) →
      Option (PanSemHOLResult (RiscV.Word 64)) × PanSemState (RiscV.Word 64) (FfiState σ)) :
    Option (PanSemHOLResult (RiscV.Word 64)) × PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprStep state expression (fun value =>
    if panShapeMatches shape (panSemShapeOf value) then
      let result := body (panSemTotalDecBind state name value)
      (result.1, { result.2 with locals := resVar result.2.locals (name, state.locals name) })
    else (some .error, state))

@[simp] theorem panSemTotalDecClause_none [BEq String] [LawfulBEq String] (state : PanSemState (RiscV.Word 64) (FfiState σ) )
    (name : VarName) (shape : Shape)
    (expression : Exp (RiscV.Word 64))
    (body : PanSemState (RiscV.Word 64) (FfiState σ) →
      Option (PanSemHOLResult (RiscV.Word 64)) × PanSemState (RiscV.Word 64) (FfiState σ))
    (heval : evalPanSemStateExp state expression = none) :
    panSemTotalDecClause state name shape expression body = (some .error, state) := by
  simp [panSemTotalDecClause, panSemTotalExprStep, heval]

theorem panSemTotalDecClause_normal [BEq String] [LawfulBEq String] (state : PanSemState (RiscV.Word 64) (FfiState σ) )
    (name : VarName) (shape : Shape)
    (expression : Exp (RiscV.Word 64))
    (body : PanSemState (RiscV.Word 64) (FfiState σ) →
      Option (PanSemHOLResult (RiscV.Word 64)) × PanSemState (RiscV.Word 64) (FfiState σ))
    (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExp state expression = some value)
    (hshape : panShapeMatches shape (panSemShapeOf value) = true) :
    panSemTotalDecClause state name shape expression body =
      (let result := body (panSemTotalDecBind state name value)
       (result.1, { result.2 with locals := resVar result.2.locals (name, state.locals name) })) := by
  simp [panSemTotalDecClause, panSemTotalExprStep, heval, hshape]

theorem panSemTotalDecClause_shapeError [BEq String] [LawfulBEq String] (state : PanSemState (RiscV.Word 64) (FfiState σ) )
    (name : VarName) (shape : Shape)
    (expression : Exp (RiscV.Word 64))
    (body : PanSemState (RiscV.Word 64) (FfiState σ) →
      Option (PanSemHOLResult (RiscV.Word 64)) × PanSemState (RiscV.Word 64) (FfiState σ))
    (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExp state expression = some value)
    (hshape : panShapeMatches shape (panSemShapeOf value) = false) :
    panSemTotalDecClause state name shape expression body = (some .error, state) := by
  simp [panSemTotalDecClause, panSemTotalExprStep, heval, hshape]

/-! ## `ShMemLoad`/`ShMemStore` total clause steps (`flapjack-pxn.18.4.3.77.9`)

HOL `evaluate` for shared-memory access (`panSemScript.sml:602-610`) evaluates the
address (and value), requires the results to be `ValWord`s, and dispatches to
`sh_mem_load`/`sh_mem_store` with the byte width `nb_op op`.  For `ShMemLoad` the
destination must already be bound to a word (`lookup_kvar vk v s = SOME (ValWord _)`).
The faithful source-level implementations live in `Flapjack/PanShMemLoad.lean`
and `Flapjack/PanShMemStore.lean`; here they are lifted onto the complete
production `PanSemState`.  Everything is untagged interface support. -/

/-- Mapped shared-memory FFI context for the executed RV64 source state. -/
abbrev panSemTotalShMemContext (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanValueFfiContext (RiscV.Word 64) :=
  riscv64PanValueFfiContext state.sharedMemaddrs

/-- Project the complete source state onto the shared-memory helper state. -/
def panSemTotalShMemState (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanShMemLoadState (RiscV.Word 64) σ where
  locals := state.locals
  globals := state.globals
  memory := state.memory
  ffi := state.ffi
  clock := state.clock

/-- Write the shared-memory helper state back into the complete source state. -/
def panSemTotalShMemStateBack (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (shState : PanShMemLoadState (RiscV.Word 64) σ) :
    PanSemState (RiscV.Word 64) (FfiState σ) :=
  { state with
    locals := shState.locals
    globals := shState.globals
    memory := shState.memory
    ffi := shState.ffi
    clock := shState.clock }

/-- Map a `sh_mem_load` outcome onto the HOL-shaped total result. -/
def panSemTotalShMemLoadResult (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanShMemLoadResult (RiscV.Word 64) σ →
      Option (PanSemHOLResult (RiscV.Word 64)) × PanSemState (RiscV.Word 64) (FfiState σ)
  | .error _ => (some .error, state)
  | .normal shState => (none, panSemTotalShMemStateBack state shState)
  | .final shState event => (some (.finalFfi event), panSemTotalShMemStateBack state shState)

/-- Map a `sh_mem_store` outcome onto the HOL-shaped total result. -/
def panSemTotalShMemStoreResult (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanShMemStoreResult (RiscV.Word 64) σ →
      Option (PanSemHOLResult (RiscV.Word 64)) × PanSemState (RiscV.Word 64) (FfiState σ)
  | .error _ => (some .error, state)
  | .normal shState => (none, panSemTotalShMemStateBack state shState)
  | .final shState event => (some (.finalFfi event), panSemTotalShMemStateBack state shState)

/-- HOL `evaluate (ShMemLoad op vk v ad, s)` clause step (`panSemScript.sml:602`). -/
def panSemTotalShMemLoadClause [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprStep state address (fun addressValue =>
    match addressValue with
    | .word addr =>
        match (match kind with
               | .local => state.locals name
               | .global => state.globals name) with
        | some (.word _) =>
            panSemTotalShMemLoadResult state
              (panShMemLoad (panSemTotalShMemContext state) (panSemTotalShMemState state)
                kind name size addr)
        | _ => (some .error, state)
    | _ => (some .error, state))

/-- HOL `evaluate (ShMemStore op ad e, s)` clause step (`panSemScript.sml:607`). -/
def panSemTotalShMemStoreClause [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (size : OpSize) (address value : Exp (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprStep state address (fun addressValue =>
    match addressValue with
    | .word addr =>
        panSemTotalExprStep state value (fun storedValue =>
          match storedValue with
          | .word bytes =>
              panSemTotalShMemStoreResult state
                (panShMemStore (panSemTotalShMemContext state) (panSemTotalShMemState state)
                  bytes addr size)
          | _ => (some .error, state))
    | _ => (some .error, state))

/-! ## Total `ExtCall` clause composition step (flapjack-pxn.18.4.3.77.15)

`panSemTotalExtCallStep` mirrors the HOL `ExtCall` case of `evaluate_def`
(`cakeml/pancake/semantics/panSemScript.sml:711-726`): evaluate the four
arguments, read two byte arrays through the two pointer/length pairs, call the
FFI, and either propagate the final event (clearing locals) or write the
returned bytes back and install the new FFI state. It is UNTAGGED
(carrier-safe infrastructure, no `@[hol]` claim): HOL's `funname` is
`mlstring` while Lean uses `String`, and the byte-array/memory codec is
supplied by the caller via callbacks. -/

/-- HOL `ExtCall` (`panSemScript.sml:711-726`). `readBytes address lengthWord`
    is HOL's `read_bytearray address (w2n lengthWord) (mem_load_byte ...)`;
    `invoke` is `call_FFI`; `writeBytes` is the total `write_bytearray` update
    of the state's memory. -/
def panSemTotalExtCallStep (state : PanSemState α (FfiState σ))
    (evaluatedPtr1 evaluatedLen1 evaluatedPtr2 evaluatedLen2 : Option (PanValue α))
    (readBytes : α → α → Option (List UInt8))
    (invoke : FfiState σ → FfiName → List UInt8 → List UInt8 → FfiResult σ)
    (writeBytes : PanSemState α (FfiState σ) → α → List UInt8 → PanSemState α (FfiState σ))
    (function : FunName) :
    Option (PanSemHOLResult α) × PanSemState α (FfiState σ) :=
  match evaluatedPtr1, evaluatedLen1, evaluatedPtr2, evaluatedLen2 with
  | some (.word address1), some (.word length1), some (.word address2),
      some (.word length2) =>
      match readBytes address1 length1, readBytes address2 length2 with
      | some bytes, some bytes2 =>
          match invoke state.ffi (.extCall function) bytes bytes2 with
          | .final event => (some (.finalFfi event), panEmptyLocals state)
          | .returned newFfi newBytes =>
              (none, { writeBytes state address2 newBytes with ffi := newFfi })
      | _, _ => (some .error, state)
  | _, _, _, _ => (some .error, state)

@[simp] theorem panSemTotalExtCallStep_none
    (state : PanSemState α (FfiState σ))
    (readBytes : α → α → Option (List UInt8))
    (invoke : FfiState σ → FfiName → List UInt8 → List UInt8 → FfiResult σ)
    (writeBytes : PanSemState α (FfiState σ) → α → List UInt8 → PanSemState α (FfiState σ))
    (function : FunName) :
    panSemTotalExtCallStep state none none none none readBytes invoke writeBytes function =
      (some .error, state) := rfl

theorem panSemTotalExtCallStep_read_error
    (state : PanSemState α (FfiState σ))
    (address1 length1 address2 length2 : α)
    (readBytes : α → α → Option (List UInt8))
    (invoke : FfiState σ → FfiName → List UInt8 → List UInt8 → FfiResult σ)
    (writeBytes : PanSemState α (FfiState σ) → α → List UInt8 → PanSemState α (FfiState σ))
    (function : FunName) (hread : readBytes address1 length1 = none) :
    panSemTotalExtCallStep state (some (.word address1)) (some (.word length1))
        (some (.word address2)) (some (.word length2)) readBytes invoke writeBytes function =
      (some .error, state) := by
  simp [panSemTotalExtCallStep, hread]

theorem panSemTotalExtCallStep_final
    (state : PanSemState α (FfiState σ))
    (address1 length1 address2 length2 : α) (bytes bytes2 : List UInt8)
    (readBytes : α → α → Option (List UInt8))
    (invoke : FfiState σ → FfiName → List UInt8 → List UInt8 → FfiResult σ)
    (writeBytes : PanSemState α (FfiState σ) → α → List UInt8 → PanSemState α (FfiState σ))
    (function : FunName) (event : FfiFinalEvent)
    (hread1 : readBytes address1 length1 = some bytes)
    (hread2 : readBytes address2 length2 = some bytes2)
    (hinvoke : invoke state.ffi (.extCall function) bytes bytes2 = .final event) :
    panSemTotalExtCallStep state (some (.word address1)) (some (.word length1))
        (some (.word address2)) (some (.word length2)) readBytes invoke writeBytes function =
      (some (.finalFfi event), panEmptyLocals state) := by
  simp [panSemTotalExtCallStep, hread1, hread2, hinvoke]

theorem panSemTotalExtCallStep_returned
    (state : PanSemState α (FfiState σ))
    (address1 length1 address2 length2 : α) (bytes bytes2 : List UInt8)
    (readBytes : α → α → Option (List UInt8))
    (invoke : FfiState σ → FfiName → List UInt8 → List UInt8 → FfiResult σ)
    (writeBytes : PanSemState α (FfiState σ) → α → List UInt8 → PanSemState α (FfiState σ))
    (function : FunName) (newFfi : FfiState σ) (newBytes : List UInt8)
    (hread1 : readBytes address1 length1 = some bytes)
    (hread2 : readBytes address2 length2 = some bytes2)
    (hinvoke : invoke state.ffi (.extCall function) bytes bytes2 = .returned newFfi newBytes) :
    panSemTotalExtCallStep state (some (.word address1)) (some (.word length1))
        (some (.word address2)) (some (.word length2)) readBytes invoke writeBytes function =
      (none, { writeBytes state address2 newBytes with ffi := newFfi }) := by
  simp [panSemTotalExtCallStep, hread1, hread2, hinvoke]


/-! ## ExtCall machine codec and clause assembly (flapjack-pxn.18.4.3.77.16)

The executable byte-array codec for the source `ExtCall`: `read_bytearray`
over the HOL-shaped `panMemLoadByteHOL` view of the executable `PanValue`
memory, and the total `panWriteBytearrayHOL` write-back mapped into that same
`PanValue` memory.  Both are UNTAGGED infrastructure (HOL's `funname` is
`mlstring` while the dispatcher uses `String`). -/

/-- HOL `read_bytearray address (w2n lengthWord) (mem_load_byte ...)` over the
    executable word-cell memory, using the total `panValueWordHOL` view. -/
def panSemTotalMachineReadBytes (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address : RiscV.Word 64) (length : RiscV.Word 64) : Option (List UInt8) :=
  readBytearrayHOL address length.toNat
    (panMemLoadByteHOL (width := 64) (panValueWordHOL state.memory)
      (fun candidate =>
        state.memaddrs candidate && panValueWordDefined state.memory candidate = true)
      state.be)

/-- HOL `write_bytearray address bytes s.memory s.memaddrs s.be` over the
    executable word-cell memory: write the bytes with the total
    `panWriteBytearrayHOL` and read the result back as word cells. -/
def panSemTotalMachineWriteBytes (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address : RiscV.Word 64) (bytes : List UInt8) :
    PanSemState (RiscV.Word 64) (FfiState σ) :=
  { state with
    memory := fun candidate =>
      some (.word (theWordHOL (panWriteBytearrayHOL address bytes
        (panValueWordHOL state.memory)
        (fun current =>
          state.memaddrs current && panValueWordDefined state.memory current = true)
        state.be candidate))) }

/-- Assemble the HOL `ExtCall` clause (`panSemScript.sml:711-726`) from the
    four evaluated argument expressions: read both byte arrays, invoke
    `call_FFI`, and either clear locals on a final event or write the returned
    bytes back and install the new FFI state. -/
def panSemTotalExtCallClause [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function : FunName)
    (configuration configurationLength array arrayLength : Exp (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprStep state configuration (fun configurationValue =>
    panSemTotalExprStep state configurationLength (fun configurationLengthValue =>
      panSemTotalExprStep state array (fun arrayValue =>
        panSemTotalExprStep state arrayLength (fun arrayLengthValue =>
          panSemTotalExtCallStep state (some configurationValue) (some configurationLengthValue)
            (some arrayValue) (some arrayLengthValue)
            (panSemTotalMachineReadBytes state)
            (fun ffi name configurationBytes arrayBytes =>
              callFfi ffi name configurationBytes arrayBytes)
            (panSemTotalMachineWriteBytes) function))))

/-- Partial assembly of the total HOL `panSem$evaluate` (`panSemScript.sml:557-655`)
    over the complete source state: dispatches the statement clauses that have
    already been assembled in this module (clock leaves `Skip`/`Break`/`Continue`/
    `Tick`, `Assign`, `Dec` with its continuation, `Primitive`, `Store`,
    `Store32`, `StoreByte`, `Raise`, `Return`, `Annot`, `ShMemLoad`,
    `ShMemStore`, `ExtCall`).

    Clauses that are not yet assembled (`Seq`, `If`, `While`, `Call`,
    `DecCall`) fall back to `SOME Error` with the state unchanged; this
    declaration is therefore not the full evaluator and is not tagged as HOL's
    `evaluate_def`.  It is the assembly step tracked by
    `flapjack-pxn.18.4.3.77.2`. -/
def panSemTotalEvaluatePartial [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)] [BEq String] [LawfulBEq String]
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (program : Prog (RiscV.Word 64)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  match program with
  | .skip => panSemEvaluateClockLeaf .skip state
  | .break => panSemEvaluateClockLeaf .break state
  | .continue => panSemEvaluateClockLeaf .continue state
  | .tick => panSemEvaluateClockLeaf .tick state
  | .assign kind name value => panSemTotalAssignClause state kind name value
  | .dec name shape value body =>
      panSemTotalDecClause state name shape value
        (fun next => panSemTotalEvaluatePartial primitive next body)
  | .primitive name operator arguments =>
      panSemTotalPrimitiveClause state name operator arguments primitive
  | .store address value => panSemTotalStoreClause state address value
  | .store32 address value => panSemTotalStore32Clause state address value
  | .storeByte address value => panSemTotalStoreByteClause state address value
  | .raise exception value => panSemTotalRaiseClause state exception value
  | .return value => panSemTotalReturnClause state value
  | .annot tag text => panSemTotalAnnotClause state tag text
  | .seq _ _ => (some .error, state)
  | .ite _ _ _ => (some .error, state)
  | .while _ _ => (some .error, state)
  | .call _ _ _ => (some .error, state)
  | .decCall _ _ _ _ _ => (some .error, state)
  | .extCall function configuration configurationLength array arrayLength =>
      panSemTotalExtCallClause state function configuration configurationLength array arrayLength
  | .shMemLoad size kind name address => panSemTotalShMemLoadClause state size kind name address
  | .shMemStore size address value => panSemTotalShMemStoreClause state size address value
termination_by sizeOf program
decreasing_by
  all_goals
    simp_wf
    omega

/-! ## Compositional `While` step (flapjack-pxn.18.4.3.77.10)

HOL `While` (`cakeml/pancake/semantics/panSemScript.sml:625-635`) is a recursive
loop.  The recursion measure (loop clock plus syntax fuel) lives in the total
evaluator, so this file records only the post-evaluation composition: given the
already evaluated condition and continuations for the body and the loop, build
the HOL outcome/state pair.  The clause is not tagged as HOL's `evaluate_def`
and `panSemTotalEvaluatePartial` still returns `some Error` for `.while` until
the recursive measure is available. -/

/-- HOL `While` (`panSemScript.sml:625-635`): a zero condition is a normal
    completion with the state unchanged; a nonzero condition at clock zero is a
    timeout with cleared locals; otherwise evaluate the body on
    `dec_clock state`, clamp the body state's clock (`fix_clock`), and recurse
    on `Continue` or normal completion, return normally on `Break`, and pass any
    other outcome through. -/
def panSemTotalWhileStep [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ))
    (evaluatedCondition : Option (PanValue α))
    (evaluateBody : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (recurseWhile : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    Option (PanSemHOLResult α) × PanSemState α (FfiState σ) :=
  match evaluatedCondition with
  | some (.word word) =>
      if word = 0 then (none, state)
      else
        if state.clock = 0 then
          (some .timeOut, { state with locals := fun _ => none })
        else
          let decremented := { state with clock := state.clock - 1 }
          let bodyResult := evaluateBody decremented
          let s1 := panSemFixClock decremented.clock bodyResult.2
          match bodyResult.1 with
          | none => recurseWhile s1
          | some .continue => recurseWhile s1
          | some .break => (none, s1)
          | other => (other, s1)
  | _ => (some .error, state)

@[simp] theorem panSemTotalWhileStep_none [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ))
    (evaluateBody : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (recurseWhile : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalWhileStep state none evaluateBody recurseWhile = (some .error, state) := rfl

@[simp] theorem panSemTotalWhileStep_rStruct [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ)) (fields : List (PanValue α))
    (evaluateBody : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (recurseWhile : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalWhileStep state (some (.rStruct fields)) evaluateBody recurseWhile =
      (some .error, state) := rfl

@[simp] theorem panSemTotalWhileStep_nStruct [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ)) (name : StructName)
    (fields : List (FieldName × PanValue α))
    (evaluateBody : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (recurseWhile : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalWhileStep state (some (.nStruct name fields)) evaluateBody recurseWhile =
      (some .error, state) := rfl

theorem panSemTotalWhileStep_word_zero [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ)) (word : α) (hzero : word = 0)
    (evaluateBody : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (recurseWhile : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalWhileStep state (some (.word word)) evaluateBody recurseWhile =
      (none, state) := by
  simp [panSemTotalWhileStep, hzero]

theorem panSemTotalWhileStep_word_timeout [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ)) (word : α) (hzero : word ≠ 0)
    (hclock : state.clock = 0)
    (evaluateBody : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (recurseWhile : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalWhileStep state (some (.word word)) evaluateBody recurseWhile =
      (some .timeOut, { state with locals := fun _ => none }) := by
  simp [panSemTotalWhileStep, hzero, hclock]

/-- The nonzero-condition, nonzero-clock body step. -/
theorem panSemTotalWhileStep_word_body [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ)) (word : α) (hzero : word ≠ 0)
    (hclock : state.clock ≠ 0)
    (evaluateBody : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (recurseWhile : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalWhileStep state (some (.word word)) evaluateBody recurseWhile =
      (let decremented := { state with clock := state.clock - 1 }
       let bodyResult := evaluateBody decremented
       let s1 := panSemFixClock decremented.clock bodyResult.2
       match bodyResult.1 with
       | none => recurseWhile s1
       | some .continue => recurseWhile s1
       | some .break => (none, s1)
       | other => (other, s1)) := by
  simp [panSemTotalWhileStep, hzero, hclock]

theorem panSemTotalWhileStep_word_break [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ)) (word : α) (hzero : word ≠ 0)
    (hclock : state.clock ≠ 0) (s1 : PanSemState α (FfiState σ))
    (evaluateBody : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (recurseWhile : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (hbody : evaluateBody { state with clock := state.clock - 1 } = (some .break, s1)) :
    panSemTotalWhileStep state (some (.word word)) evaluateBody recurseWhile =
      (none, panSemFixClock (state.clock - 1) s1) := by
  rw [panSemTotalWhileStep_word_body state word hzero hclock evaluateBody recurseWhile]
  simp [hbody]

theorem panSemTotalWhileStep_word_continue [DecidableEq α] [OfNat α 0]
    (state : PanSemState α (FfiState σ)) (word : α) (hzero : word ≠ 0)
    (hclock : state.clock ≠ 0) (s1 : PanSemState α (FfiState σ))
    (evaluateBody : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (recurseWhile : PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (hbody : evaluateBody { state with clock := state.clock - 1 } = (some .continue, s1)) :
    panSemTotalWhileStep state (some (.word word)) evaluateBody recurseWhile =
      recurseWhile (panSemFixClock (state.clock - 1) s1) := by
  rw [panSemTotalWhileStep_word_body state word hzero hclock evaluateBody recurseWhile]
  simp [hbody]

/-! ## Flapjack panSem clock helpers (flapjack-pxn.18.4.3.77.11)

`panSem$dec_clock_def` and `panSem$fix_clock_def`
(`cakeml/pancake/semantics/panSemScript.sml:441/446`) are the clock-only
state operations used by the recursive `evaluate` clauses. The bodies here are
clause-for-clause copies, but the `@[hol]` tags are **withdrawn**: the carrier
`PanSemHolState` is a String-backed source projection (its `locals`/`globals`
are `VarName`-keyed, `code` is `FunName`-keyed, `eshapes` is
`ExceptionId`-keyed, `structs : StructContextHOL`, and `locals` values are
`HolValue`, whose `nStruct` names/fields are `StructName`/`FieldName` = String),
while HOL's `'a` word / `mlstring` carriers are exact only once the MlString
state carrier lands (tracked by `flapjack-pxn.18.3.5.8`, exact port bead
`flapjack-pxn.18.4.3.77.11.1`, carrier audit `docs/PANSEM-CARRIER-AUDIT.md`). -/

/-- FLAPJACK-SPECIFIC (not a statement-exact HOL port): `dec_clock s = s with
    clock := s.clock - 1` over the word-indexed source projection
    `PanSemHolState width σ`; tag withheld for the String carrier reason above. -/
def decClockHOL {width : Nat} [NeZero width] (state : PanSemHolState width σ) :
    PanSemHolState width σ :=
  { state with clock := state.clock - 1 }

/-- FLAPJACK-SPECIFIC (not a statement-exact HOL port): the result component is
    threaded through unchanged (RESULT-POLYMORPHIC in `β`, as HOL's `fix_clock`
    leaves `res` unconstrained) and the returned clock is clamped to the smaller
    of the old and new clocks; tag withheld for the String carrier reason above. -/
def fixClockHOL {width : Nat} [NeZero width] {β : Type} (oldState : PanSemHolState width σ)
    (step : β × PanSemHolState width σ) : β × PanSemHolState width σ :=
  (step.1, { step.2 with
    clock := if oldState.clock < step.2.clock then oldState.clock else step.2.clock })

/-! ## Total `DecCall` clause composition step (flapjack-pxn.18.4.3.77.13)

`panSemTotalDecCallStep` mirrors the HOL `DecCall` case of `evaluate_def`
(`cakeml/pancake/semantics/panSemScript.sml:679-706`): evaluate the arguments,
look the callee up, raise a timeout at clock zero, otherwise evaluate the body
on the decremented state with the callee's locals and the clock clamped by
`fix_clock`, then handle the body outcome. It is UNTAGGED (carrier-safe
infrastructure, no `@[hol]` claim): HOL's `varname`/`funname` are `mlstring`
while Lean uses `String`. -/

/-- HOL `DecCall` (`panSemScript.sml:679-706`). The arguments, the callee
    lookup result, the result binding name/shape, the continuation program, and
    the recursive evaluator are all supplied explicitly, so the step is a pure
    composition. On a `Return` whose shape matches both the declared result
    shape and the callee's return shape, the continuation runs on the bound
    result and the previous local binding of the result name is restored with
    `res_var`. -/
def panSemTotalDecCallStep [BEq String] [LawfulBEq String]
    (state : PanSemState α (FfiState σ))
    (evaluatedArguments : Option (List (PanValue α)))
    (lookup : Option (Prog α × (VarName → Option (PanValue α)) × Shape))
    (resultName : VarName) (resultShape : Shape) (continuation : Prog α)
    (evaluate : Prog α → PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    Option (PanSemHOLResult α) × PanSemState α (FfiState σ) :=
  match evaluatedArguments, lookup with
  | some _, some (body, newLocals, returnShape) =>
      if state.clock = 0 then (some .timeOut, panEmptyLocals state)
      else
        let entry : PanSemState α (FfiState σ) :=
          { state with clock := state.clock - 1, locals := newLocals }
        let bodyResult := evaluate body entry
        let fixed : Option (PanSemHOLResult α) × PanSemState α (FfiState σ) :=
          (bodyResult.1, panSemFixClock entry.clock bodyResult.2)
        match fixed.1 with
        | none => (some .error, fixed.2)
        | some .break => (some .error, fixed.2)
        | some .continue => (some .error, fixed.2)
        | some (.returned value) =>
            if panShapeMatches resultShape (panSemShapeOf value) &&
                panShapeMatches resultShape returnShape then
              let bound : PanSemState α (FfiState σ) :=
                { fixed.2 with
                  locals := updatePanValueMap state.locals resultName value }
              let continuationResult := evaluate continuation bound
              (continuationResult.1,
                { continuationResult.2 with
                  locals := resVar continuationResult.2.locals
                    (resultName, state.locals resultName) })
            else (some .error, fixed.2)
        | some other => (some other, panEmptyLocals fixed.2)
  | _, _ => (some .error, state)

@[simp] theorem panSemTotalDecCallStep_none_args [BEq String] [LawfulBEq String]
    (state : PanSemState α (FfiState σ))
    (lookup : Option (Prog α × (VarName → Option (PanValue α)) × Shape))
    (resultName : VarName) (resultShape : Shape) (continuation : Prog α)
    (evaluate : Prog α → PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalDecCallStep state none lookup resultName resultShape continuation evaluate =
      (some .error, state) := rfl

@[simp] theorem panSemTotalDecCallStep_none_lookup [BEq String] [LawfulBEq String]
    (state : PanSemState α (FfiState σ)) (arguments : List (PanValue α))
    (resultName : VarName) (resultShape : Shape) (continuation : Prog α)
    (evaluate : Prog α → PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalDecCallStep state (some arguments) none resultName resultShape
      continuation evaluate = (some .error, state) := rfl

theorem panSemTotalDecCallStep_timeout [BEq String] [LawfulBEq String]
    (state : PanSemState α (FfiState σ)) (arguments : List (PanValue α))
    (body : Prog α) (newLocals : VarName → Option (PanValue α)) (returnShape : Shape)
    (resultName : VarName) (resultShape : Shape) (continuation : Prog α)
    (evaluate : Prog α → PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (hclock : state.clock = 0) :
    panSemTotalDecCallStep state (some arguments) (some (body, newLocals, returnShape))
        resultName resultShape continuation evaluate =
      (some .timeOut, panEmptyLocals state) := by
  simp [panSemTotalDecCallStep, hclock]

/-! ## Total `Call` clause composition step (flapjack-pxn.18.4.3.77.14)

`panSemTotalCallStep` mirrors the HOL `Call` case of `evaluate_def`
(`cakeml/pancake/semantics/panSemScript.sml:658-697`): like `DecCall` for the
arguments/lookup/clock/body handling, plus the `caltyp` destination and
exception-handler dispatch. It is UNTAGGED carrier-safe infrastructure. -/

/-- HOL `Call` (`panSemScript.sml:658-697`). Returns handled with `caltyp`
    `NONE` propagate as a `Return` with cleared locals; `SOME (NONE, _)` yields
    the body state with the caller's locals; `SOME (SOME (rk, rt), _)` binds the
    result through `is_valid_value`/`set_kvar`. Raised exceptions propagate with
    cleared locals unless `caltyp` carries a matching handler, in which case the
    handler program is evaluated on the exception bound in the caller's locals
    and validated against `state.exceptionShapes`. -/
def panSemTotalCallStep [BEq String] [LawfulBEq String]
    (state : PanSemState α (FfiState σ))
    (evaluatedArguments : Option (List (PanValue α)))
    (lookup : Option (Prog α × (VarName → Option (PanValue α)) × Shape))
    (callType : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (evaluate : Prog α → PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    Option (PanSemHOLResult α) × PanSemState α (FfiState σ) :=
  match evaluatedArguments, lookup with
  | some _, some (body, newLocals, returnShape) =>
      if state.clock = 0 then (some .timeOut, panEmptyLocals state)
      else
        let entry : PanSemState α (FfiState σ) :=
          { state with clock := state.clock - 1, locals := newLocals }
        let bodyResult := evaluate body entry
        let fixed : Option (PanSemHOLResult α) × PanSemState α (FfiState σ) :=
          (bodyResult.1, panSemFixClock entry.clock bodyResult.2)
        match fixed.1 with
        | none => (some .error, fixed.2)
        | some .break => (some .error, fixed.2)
        | some .continue => (some .error, fixed.2)
        | some (.returned value) =>
            if panShapeMatches (panSemShapeOf value) returnShape then
              match callType with
              | none => (some (.returned value), panEmptyLocals fixed.2)
              | some (none, _) => (none, { fixed.2 with locals := state.locals })
              | some (some (kind, name), _) =>
                  if panValueAssignmentValid state.structs state.locals state.globals
                      kind name value then
                    (none, match kind with
                      | .local => { fixed.2 with
                          locals := updatePanValueMap state.locals name value }
                      | .global => { fixed.2 with
                          locals := state.locals,
                          globals := updatePanValueMap fixed.2.globals name value })
                  else (some .error, fixed.2)
            else (some .error, fixed.2)
        | some (.exception exceptionId value) =>
            match callType with
            | none => (some (.exception exceptionId value), panEmptyLocals fixed.2)
            | some (_, none) => (some (.exception exceptionId value), panEmptyLocals fixed.2)
            | some (_, some (handlerId, handlerVar, handlerProg)) =>
                if exceptionId == handlerId then
                  match state.exceptionShapes exceptionId with
                  | some shape =>
                      if panShapeMatches (panSemShapeOf value) shape &&
                          panValueAssignmentValid state.structs state.locals state.globals
                            .local handlerVar value then
                        evaluate handlerProg
                          { fixed.2 with
                            locals := updatePanValueMap state.locals handlerVar value }
                      else (some .error, fixed.2)
                  | none => (some .error, fixed.2)
                else (some (.exception exceptionId value), panEmptyLocals fixed.2)
        | some other => (some other, panEmptyLocals fixed.2)
  | _, _ => (some .error, state)

@[simp] theorem panSemTotalCallStep_none_args [BEq String] [LawfulBEq String]
    (state : PanSemState α (FfiState σ))
    (lookup : Option (Prog α × (VarName → Option (PanValue α)) × Shape))
    (callType : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (evaluate : Prog α → PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalCallStep state none lookup callType evaluate = (some .error, state) := rfl

@[simp] theorem panSemTotalCallStep_none_lookup [BEq String] [LawfulBEq String]
    (state : PanSemState α (FfiState σ)) (arguments : List (PanValue α))
    (callType : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (evaluate : Prog α → PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ)) :
    panSemTotalCallStep state (some arguments) none callType evaluate =
      (some .error, state) := rfl

theorem panSemTotalCallStep_timeout [BEq String] [LawfulBEq String]
    (state : PanSemState α (FfiState σ)) (arguments : List (PanValue α))
    (body : Prog α) (newLocals : VarName → Option (PanValue α)) (returnShape : Shape)
    (callType : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (evaluate : Prog α → PanSemState α (FfiState σ) →
      Option (PanSemHOLResult α) × PanSemState α (FfiState σ))
    (hclock : state.clock = 0) :
    panSemTotalCallStep state (some arguments) (some (body, newLocals, returnShape))
        callType evaluate = (some .timeOut, panEmptyLocals state) := by
  simp [panSemTotalCallStep, hclock]

end Flapjack
