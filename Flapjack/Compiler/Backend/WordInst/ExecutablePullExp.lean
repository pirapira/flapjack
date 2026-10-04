import Flapjack.Compiler.Backend.WordInst

/-! Flapjack execution infrastructure for the exact native instruction selector.
The source `pull_exp` handles subtraction before `optimize_consts`; all remaining
`word_op` clauses return `SOME`. These definitions compute that reachable path
without assigning any value to HOL's unspecified `THE NONE`. The unconditional
agreement theorem below covers every native expression, including malformed
subtraction lists. The original tagged declarations remain unchanged. -/

namespace Flapjack.Compiler.Backend.WordInst.ExecutablePullExp
open Flapjack

/-- Constructive value of a non-subtraction word operation. The proof excludes
only the unreachable optimizer branch; it is not a premise of full pullExp
agreement. Untagged execution infrastructure, with no separate HOL original. -/
def nonSubWordOp {width : Nat} (op : BinOp) (h : op ≠ .sub)
    (ws : List (BitVec width)) : BitVec width :=
  match op with
  | .add => ws.foldr (· + ·) 0
  | .and => ws.foldr (fun a b => AndOp.and a b) (~~~0)
  | .or => ws.foldr (fun a b => OrOp.or a b) 0
  | .xor => ws.foldr (· ^^^ ·) 0
  | .sub => False.elim (h rfl)

/-- Reachable `word_op` calls succeed; no undefined-value policy is needed.
Flapjack infrastructure derived directly from the native operator clauses. -/
theorem nonSubWordOp_some {width : Nat} [NeZero width]
    (op : BinOp) (h : op ≠ .sub) (ws : List (BitVec width)) :
    wordOpHOL op ws = some (nonSubWordOp op h ws) := by
  cases op <;> first | exact False.elim (h rfl) | rfl

/-- Executable optimizer on precisely the operator domain reached by pullExp.
Uses the original partition order and reductions; no claim about THE NONE. -/
def optimizeNonSub {width : Nat} [NeZero width] (op : BinOp) (h : op ≠ .sub)
    (ls : List (WordLangExpHOL (BitVec width))) : WordLangExpHOL (BitVec width) :=
  let (constLs, nconstLs) := holPartition (fun e => isConst e) ls
  match constLs with
  | [] => .op op nconstLs
  | _ => reduceConst op (nonSubWordOp op h (constLs.map rmConst)) nconstLs

/-- Unconditional on operand lists, with only the actual non-Sub call-domain
condition. This is internal computation agreement, not a new HOL theorem port. -/
theorem optimizeNonSub_eq {width : Nat} [NeZero width]
    (op : BinOp) (h : op ≠ .sub) (ls : List (WordLangExpHOL (BitVec width))) :
    optimizeNonSub op h ls = optimizeConsts op ls := by
  unfold optimizeNonSub optimizeConsts
  cases holPartition (fun e => isConst e) ls with
  | mk cs ns =>
    cases cs <;> simp [nonSubWordOp_some op h, holThe]

/-- Executable full native expression normalization, preserving all source
clauses. Untagged implementation infrastructure related to pullExp below. -/
def pullExpExecutable {width : Nat} [NeZero width] :
    WordLangExpHOL (BitVec width) → WordLangExpHOL (BitVec width)
  | .op op ls =>
      if h : op = .sub then
        convertSub (ls.attach.map (fun ⟨e, _⟩ => pullExpExecutable e))
      else
        match ls with
        | [] => opConsts op
        | [x] => pullExpExecutable x
        | x :: y :: rest =>
          let newLs := (x :: y :: rest).attach.map (fun ⟨e, _⟩ => pullExpExecutable e)
          optimizeNonSub op h (pullOps op newLs [])
  | .load exp => .load (pullExpExecutable exp)
  | .shift shift exp nexp =>
      .shift shift (pullExpExecutable exp) (pullExpExecutable nexp)
  | exp => exp
termination_by e => sizeOf e
decreasing_by
  all_goals (try subst_vars)
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | omega

/-- Full computation agreement for every positive-width native expression.
No well-formedness, successful evaluation, target run or result is assumed.
This relates two Lean implementations; original HOL captures are independent
regression evidence rather than a cross-language equivalence proof. -/
theorem pullExpExecutable_eq {width : Nat} [NeZero width]
    (exp : WordLangExpHOL (BitVec width)) : pullExpExecutable exp = pullExp exp := by
  refine (measure (sizeOf : WordLangExpHOL (BitVec width) → Nat)).wf.induction (C := fun e => pullExpExecutable e = pullExp e) exp ?_
  intro exp ih
  cases exp with
  | op op ls =>
    have hm : ls.map pullExpExecutable = ls.map pullExp := by
      apply List.map_congr_left
      intro e he
      apply ih e
      change sizeOf e < sizeOf (WordLangExpHOL.op op ls)
      have := List.sizeOf_lt_of_mem he
      simp_wf
      omega
    cases op <;> cases ls with
    | nil => simp [pullExpExecutable, pullExp]
    | cons a rest =>
      cases rest with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
        simp [pullExpExecutable, pullExp, hm]
      | cons b rest =>
        simp only [pullExpExecutable, pullExp, List.map_attach_eq_pmap,
          List.pmap_eq_map, optimizeNonSub_eq]
        rw [hm]
        simp
  | load e =>
    rw [pullExpExecutable, pullExp, ih e (by change sizeOf e < sizeOf (WordLangExpHOL.load e); simp_wf; try omega)]
  | shift sh e n =>
    rw [pullExpExecutable, pullExp,
      ih e (by change sizeOf e < sizeOf (WordLangExpHOL.shift sh e n); simp_wf; try omega),
      ih n (by change sizeOf n < sizeOf (WordLangExpHOL.shift sh e n); simp_wf; try omega)]
  | const _ | var _ | lookup _ => simp [pullExpExecutable, pullExp]

end Flapjack.Compiler.Backend.WordInst.ExecutablePullExp
