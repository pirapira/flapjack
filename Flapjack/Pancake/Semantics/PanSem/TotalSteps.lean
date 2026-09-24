import Flapjack.Pancake.Semantics.PanSem.Total

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
agreement with the tagged exact `evalHOL` is proved in
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

/-- HOL `Return` (`panSemScript.sml:625-627`): evaluate the source and return
    `SOME (Return v)` with the state unchanged, or `SOME Error` when the source
    fails. -/
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
  panSemTotalExprStep state expression (fun value => (some (.returned value), state))

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
    panSemTotalReturnClause state expression = (some (.returned value), state) := by
  simp [panSemTotalReturnClause, panSemTotalExprStep, heval]

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

/-- HOL `Raise` (`panSemScript.sml:628-630`): evaluate the source and return
    `SOME (Exception eid v)` with the state unchanged, or `SOME Error` when the
    source fails. -/
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
  panSemTotalExprStep state expression
    (fun value => (some (.exception exceptionId value), state))

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
    (heval : evalPanSemStateExp state expression = some value) :
    panSemTotalRaiseClause state exceptionId expression =
      (some (.exception exceptionId value), state) := by
  simp [panSemTotalRaiseClause, panSemTotalExprStep, heval]

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

/-- HOL `Dec` (`panSemScript.sml:556-561`): evaluate the initialiser, require
    `is_valid_value`, bind the variable through `set_kvar`, and continue with the
    body `c`; a failed initialiser or invalid binding is `SOME Error` with the
    state unchanged.  The body continuation is supplied by the eventual clause
    assembly. -/
def panSemTotalDecClause [NeZero 64] [BEq (RiscV.Word 64)]
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
    (body : PanSemState (RiscV.Word 64) (FfiState σ) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ)) :
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalExprStep state expression (fun value =>
    if panValueAssignmentValid state.structs state.locals state.globals kind name value then
      body
        (match kind with
        | .local => { state with locals := updatePanValueMap state.locals name value }
        | .global => { state with globals := updatePanValueMap state.globals name value })
    else
      (some .error, state))

@[simp] theorem panSemTotalDecClause_none [NeZero 64] [BEq (RiscV.Word 64)]
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
    (body : PanSemState (RiscV.Word 64) (FfiState σ) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ))
    (heval : evalPanSemStateExp state expression = none) :
    panSemTotalDecClause state kind name expression body = (some .error, state) := by
  simp [panSemTotalDecClause, panSemTotalExprStep, heval]

theorem panSemTotalDecClause_normal [NeZero 64] [BEq (RiscV.Word 64)]
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
    (body : PanSemState (RiscV.Word 64) (FfiState σ) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ))
    (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExp state expression = some value)
    (hvalid : panValueAssignmentValid state.structs state.locals state.globals
      kind name value = true) :
    panSemTotalDecClause state kind name expression body =
      body
        (match kind with
        | .local => { state with locals := updatePanValueMap state.locals name value }
        | .global => { state with globals := updatePanValueMap state.globals name value }) := by
  cases kind <;> simp [panSemTotalDecClause, panSemTotalExprStep, heval, hvalid]

theorem panSemTotalDecClause_invalid [NeZero 64] [BEq (RiscV.Word 64)]
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
    (body : PanSemState (RiscV.Word 64) (FfiState σ) →
      Option (PanSemHOLResult (RiscV.Word 64)) ×
        PanSemState (RiscV.Word 64) (FfiState σ))
    (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExp state expression = some value)
    (hvalid : panValueAssignmentValid state.structs state.locals state.globals
      kind name value = false) :
    panSemTotalDecClause state kind name expression body = (some .error, state) := by
  simp [panSemTotalDecClause, panSemTotalExprStep, heval, hvalid]

end Flapjack
