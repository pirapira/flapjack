import Flapjack.Pancake.Semantics.PanSem.DecCallExact

/-! # Exact HOL panSem control-flow clause steps over the exact MlString state

This module ports the structural control-flow clauses of HOL
`panSemScript.sml:evaluate_def` (lines 615-655) over the exact, `mlstring`-keyed
`PanSemStateExact` carrier and the exact `ProgHOL`/`ExpHOL`/`ValueHOL` syntax:

* `Seq c1 c2`: `let (res, s1) = fix_clock s (evaluate (c1, s))` then continue with
  `c2` exactly when `res = NONE`, otherwise return `(res, s1)`;
* `If e c1 c2`: `case eval s e of SOME (ValWord w) => evaluate (if w <> 0w then c1
  else c2, s) | _ => (SOME Error, s)`;
* `While e c`: on a nonzero word, `clock = 0` gives `(SOME TimeOut, empty_locals s)`,
  otherwise `fix_clock (dec_clock s) (evaluate (c, dec_clock s))` is inspected:
  `SOME Continue` and `NONE` recurse, `SOME Break` gives `(NONE, s1)`, anything else
  is returned unchanged; a zero word gives `(NONE, s)`;
* `Break`/`Continue`: `(SOME Break, s)`/`(SOME Continue, s)`;
* `Annot _ _`: `(NONE, s)`.

The clause steps take explicit `evaluate` callbacks (and `recurseWhile` for the
`While` loop), so they are untagged infrastructure: only the whole
`evaluate_def` conjunction, once assembled, would be the exact HOL statement. The
direct original-HOL rows are recorded in
`scripts/hol-probes/pan_sem_e2e_probe.out` (rows `seq_two_assigns`,
`seq_first_errors`, `if_true`, `if_false`, `if_error`, `while_cond_zero`,
`while_timeout`, `while_break`, `while_continue_then_zero`,
`while_error_condition`, `break_clause`, `continue_clause`, `annot_clause`) and
replayed by `Flapjack/Test/PanSemControlExactParity.lean`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ExpHOL ProgHOL)

/-- Exact `Seq` clause step: run `first`, keep the clock fixed, and continue with
`second` only on normal completion (`NONE`). -/
def seqStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (first second : ProgHOL width)
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  let result := fixClockHOLExact state (evaluate first state)
  match result.1 with
  | none => evaluate second result.2
  | some _ => result

/-- Exact `If` clause step: a `ValWord` condition selects the branch (zero is
false); any other evaluation result is an error. -/
def ifStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (condition : ExpHOL width)
    (thenBranch elseBranch : ProgHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state condition with
  | some (.val (.word word)) =>
      evaluate (if word ≠ 0 then thenBranch else elseBranch) state
  | _ => (some .error, state)

/-- Exact `While` clause step: a zero condition exits normally, a nonzero
condition at `clock = 0` times out and clears the locals, otherwise the body runs
on `dec_clock s` under `fix_clock` and `Continue`/normal completion recurse while
`Break` exits normally. -/
def whileStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (condition : ExpHOL width) (body : ProgHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (recurseWhile : PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state condition with
  | some (.val (.word word)) =>
      if word ≠ 0 then
        if state.clock = 0 then
          (some .timeOut, emptyLocalsHOLExact state)
        else
          let entry := decClockHOLExact state
          let result := fixClockHOLExact entry (evaluate body entry)
          match result.1 with
          | some .continue => recurseWhile result.2
          | none => recurseWhile result.2
          | some .break => (none, result.2)
          | _ => result
      else (none, state)
  | _ => (some .error, state)

/-- Exact `Break` clause. -/
def breakStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  (some .break, state)

/-- Exact `Continue` clause. -/
def continueStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  (some .continue, state)

/-- Exact `Annot` clause: annotations are transparent. -/
def annotStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (_tag _text : MlS) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  (none, state)

@[simp] theorem breakStepHOLExact_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    breakStepHOLExact state = (some .break, state) := rfl

@[simp] theorem continueStepHOLExact_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    continueStepHOLExact state = (some .continue, state) := rfl

@[simp] theorem annotStepHOLExact_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (tag text : MlS) :
    annotStepHOLExact state tag text = (none, state) := rfl

theorem ifStepHOLExact_word {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (condition : ExpHOL width)
    (thenBranch elseBranch : ProgHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (word : RiscV.Word width)
    (h : evalExpression state condition = some (.val (.word word))) :
    ifStepHOLExact state condition thenBranch elseBranch evalExpression evaluate =
      evaluate (if word ≠ 0 then thenBranch else elseBranch) state := by
  simp only [ifStepHOLExact, h]

theorem ifStepHOLExact_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (condition : ExpHOL width)
    (thenBranch elseBranch : ProgHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (h : evalExpression state condition = none) :
    ifStepHOLExact state condition thenBranch elseBranch evalExpression evaluate =
      (some .error, state) := by
  simp only [ifStepHOLExact, h]

theorem whileStepHOLExact_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (condition : ExpHOL width) (body : ProgHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (recurseWhile : PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (h : evalExpression state condition = none) :
    whileStepHOLExact state condition body evalExpression evaluate recurseWhile =
      (some .error, state) := by
  simp only [whileStepHOLExact, h]

theorem whileStepHOLExact_zero {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (condition : ExpHOL width) (body : ProgHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (recurseWhile : PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (word : RiscV.Word width)
    (h : evalExpression state condition = some (.val (.word word))) (hzero : word = 0) :
    whileStepHOLExact state condition body evalExpression evaluate recurseWhile =
      (none, state) := by
  simp [whileStepHOLExact, h, hzero]

theorem whileStepHOLExact_timeout {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (condition : ExpHOL width) (body : ProgHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (evaluate : ProgHOL width → PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (recurseWhile : PanSemStateExact width σ →
      Option (PanSemResultExact width) × PanSemStateExact width σ)
    (word : RiscV.Word width)
    (h : evalExpression state condition = some (.val (.word word))) (hne : word ≠ 0)
    (hclock : state.clock = 0) :
    whileStepHOLExact state condition body evalExpression evaluate recurseWhile =
      (some .timeOut, emptyLocalsHOLExact state) := by
  simp only [whileStepHOLExact, h]
  rw [if_pos hne, if_pos hclock]

end Flapjack
