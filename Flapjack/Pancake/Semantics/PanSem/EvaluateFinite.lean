/-
FINITE-SUPPORT CARRIER PROGRAM EVALUATION (flapjack-6yq / flapjack-qj5).

The exact `evaluate_def` evaluator `evalPanSemRecursiveCallContextHOLExact`
(`TotalEvalExact.lean`) quantifies over `PanSemStateExact`, whose
`locals`/`globals`/`code`/`eshapes` are unrestricted `MlS → Option _` functions.
HOL `panSem$state` instead keeps those fields as finite maps (`varname |-> 'a v`,
`|->`), so the evaluator is faithful only on the finite-support subcarrier.

`PanSemStateFiniteExact.evaluateHOLFinite` (in the carrier module
`StateExactFiniteMap.lean`) is the provisional state-level projection of the
direct, clause-for-clause finite context evaluator
`evalPanSemRecursiveCallFiniteContext`.  It currently keeps the outer `Option`
assembly marker (the marker is always `some` once totality is proved; bead
`flapjack-6yq`), so a clause returns `some (result, state)` rather than HOL
`evaluate_def`'s bare `result option × state` pair.  The finite
context threads `memaddrsDecidable`/`shMemaddrsDecidable` (bead `flapjack-6yq`)
so the recursive clauses typecheck over literal record updates.

This module exposes the clause surface of `evaluateHOLFinite`, clause by clause,
as the source evidence for the `evaluate_def` port.  Exposed so far:
`Skip` / `Break` / `Continue`, and the `Seq` (three outcomes) and `If`
(then/else on a word condition) clauses.  The remaining clauses are being
added; the exact `@[hol ... "evaluate_def" ...]` tag stays withheld until every
clause is exposed and reviewed (`flapjack-qj5` is blocked on `flapjack-6yq`).

The older delegating adapter `evaluateHOLFiniteViaExact` (and its
`evalPanSemRecursiveCallHOLFinite_of_broad` / `evaluateHOLFiniteViaExact_of_broad`
translation lemmas) remains as untagged Flapjack-specific infrastructure.
-/
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace Flapjack

open Flapjack.Pancake.PanLang (ProgHOL ExpHOL MlS ShapeHOL)

namespace PanSemStateFiniteExact

/-- Generic translation: given the broad exact evaluator's result on `program`,
    the finite recursive evaluator returns the same result with the post-state
    rebuilt through the canonical finite-support carrier. -/
theorem evalPanSemRecursiveCallHOLFinite_of_broad {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemExactEvalContext width σ)
    (hb : evalPanSemRecursiveCallContextHOLExact program
        { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
      some output) :
    evalPanSemRecursiveCallHOLFinite state program =
      some (output.1, ofExact output.2.state
        (evalPanSemRecursiveCallContextHOLExact_finiteSupport program
          { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }
          state.toExact_finiteSupport output hb)) := by
  rw [evalPanSemRecursiveCallHOLFinite.eq_def]
  dsimp only
  split
  · rename_i hres
    rw [hb] at hres
    simp at hres
  · rename_i pair hres
    rw [hb] at hres
    simp only [Option.some.injEq] at hres
    subst hres
    rfl

/-- Generic translation for the finite adapter: given the broad exact
    evaluator's result on `program`, `evaluateHOLFiniteViaExact` returns the same
    (`result option × state`) pair with the post-state rebuilt through the
    canonical finite-support carrier. -/
theorem evaluateHOLFiniteViaExact_of_broad {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs]
    (program : ProgHOL width)
    (output : Option (PanSemResultExact width) × PanSemExactEvalContext width σ)
    (hb : evalPanSemRecursiveCallContextHOLExact program
        { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
      some output) :
    evaluateHOLFiniteViaExact state program =
      (output.1, ofExact output.2.state
        (evalPanSemRecursiveCallContextHOLExact_finiteSupport program
          { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }
          state.toExact_finiteSupport output hb)) := by
  have hw := evalPanSemRecursiveCallHOLFinite_of_broad state program output hb
  unfold evaluateHOLFiniteViaExact
  dsimp only
  rw [hw]

/-- HOL `evaluate_def` `Skip` clause: `evaluate (Skip, s) = (NONE, s)`. -/
@[simp] theorem evaluateHOLFiniteViaExact_skip {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFiniteViaExact state (.skip : ProgHOL width) = (none, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.skip : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (none, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFiniteViaExact_of_broad state _ _ hb]
  simp only [ofExact_toExact]

/-- HOL `evaluate_def` `Break` clause: `evaluate (Break, s) = (SOME Break, s)`. -/
@[simp] theorem evaluateHOLFiniteViaExact_break {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFiniteViaExact state (.break : ProgHOL width) = (some .break, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.break : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (some .break, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFiniteViaExact_of_broad state _ _ hb]
  simp only [ofExact_toExact]

/-- HOL `evaluate_def` `Continue` clause: `evaluate (Continue, s) = (SOME Continue, s)`. -/
@[simp] theorem evaluateHOLFiniteViaExact_continue {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFiniteViaExact state (.continue : ProgHOL width) = (some .continue, state) := by
  have hb : evalPanSemRecursiveCallContextHOLExact (.continue : ProgHOL width)
      { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared } =
        some (some .continue, { state := state.toExact, memaddrsDecidable := h, shMemaddrsDecidable := hshared }) := by
    rw [evalPanSemRecursiveCallContextHOLExact.eq_def]
  rw [evaluateHOLFiniteViaExact_of_broad state _ _ hb]
  simp only [ofExact_toExact]

/-- HOL `evaluate_def` `Skip` clause over the direct finite context evaluator. -/
@[simp] theorem evaluateHOLFinite_skip {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.skip : ProgHOL width) = some (none, state) := by
  unfold evaluateHOLFinite
  simp [evalPanSemRecursiveCallFiniteContext]

/-- HOL `evaluate_def` `Break` clause over the direct finite context evaluator. -/
@[simp] theorem evaluateHOLFinite_break {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.break : ProgHOL width) = some (some .break, state) := by
  unfold evaluateHOLFinite
  simp [evalPanSemRecursiveCallFiniteContext]

/-- HOL `evaluate_def` `Continue` clause over the direct finite context evaluator. -/
@[simp] theorem evaluateHOLFinite_continue {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs] [hshared : DecidablePred state.shMemaddrs] :
    evaluateHOLFinite state (.continue : ProgHOL width) = some (some .continue, state) := by
  unfold evaluateHOLFinite
  simp [evalPanSemRecursiveCallFiniteContext]

/-- HOL `evaluate_def` `Seq` clause: if the first command returns `NONE`
    (a short-circuit `Break`/`Continue`/`Return`-less normal prefix), the whole
    sequence has no result. -/
theorem evalPanSemRecursiveCallFiniteContext_seq_none {width : Nat} {σ : Type} [NeZero width]
    (first second : ProgHOL width) (context : FiniteEvalContext width σ)
    (hfirst : evalPanSemRecursiveCallFiniteContext first context = none) :
    evalPanSemRecursiveCallFiniteContext (.seq first second) context = none := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hfirst]

/-- HOL `evaluate_def` `Seq` clause: a normal (`NONE`) first result runs the
    second command from the clock-fixed continuation state. -/
theorem evalPanSemRecursiveCallFiniteContext_seq_some_none {width : Nat} {σ : Type}
    [NeZero width]
    (first second : ProgHOL width) (context : FiniteEvalContext width σ)
    (firstContext : FiniteEvalContext width σ)
    (hfirst : evalPanSemRecursiveCallFiniteContext first context = some (none, firstContext)) :
    evalPanSemRecursiveCallFiniteContext (.seq first second) context =
      evalPanSemRecursiveCallFiniteContext second
        (firstContext.withState
          (fixClockHOLFinite context.state
            ((none : Option (PanSemResultExact width)), firstContext.state)).2 rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hfirst]

/-- HOL `evaluate_def` `Seq` clause: a non-`NONE` first result short-circuits the
    sequence at the clock-fixed continuation state. -/
theorem evalPanSemRecursiveCallFiniteContext_seq_some_some {width : Nat} {σ : Type}
    [NeZero width]
    (first second : ProgHOL width) (context : FiniteEvalContext width σ)
    (firstContext : FiniteEvalContext width σ)
    (firstResult : PanSemResultExact width)
    (hfirst : evalPanSemRecursiveCallFiniteContext first context =
      some (some firstResult, firstContext)) :
    evalPanSemRecursiveCallFiniteContext (.seq first second) context =
      some (some firstResult,
        firstContext.withState
          (fixClockHOLFinite context.state (some firstResult, firstContext.state)).2 rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hfirst]

/-- HOL `evaluate_def` `If` clause, non-zero branch: a word-valued true condition
    selects the then-branch. -/
theorem evalPanSemRecursiveCallFiniteContext_ite_then {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (value : BitVec width)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word value)))
    (hne : (value != 0) = true) :
    evalPanSemRecursiveCallFiniteContext (.ite condition thenBranch elseBranch) context =
      evalPanSemRecursiveCallFiniteContext thenBranch context := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_pos hne]

/-- HOL `evaluate_def` `If` clause, zero branch: a word-valued false condition
    selects the else-branch. -/
theorem evalPanSemRecursiveCallFiniteContext_ite_else {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (value : BitVec width)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word value)))
    (hz : (value != 0) = false) :
    evalPanSemRecursiveCallFiniteContext (.ite condition thenBranch elseBranch) context =
      evalPanSemRecursiveCallFiniteContext elseBranch context := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_neg (by rw [hz]; decide)]

/-- HOL `evaluate_def` `Dec` clause: an initializer that fails to evaluate yields
    the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_dec_init_none {width : Nat} {σ : Type}
    [NeZero width]
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (hinit : evalHOLFinite context.state (h := context.memaddrsDecidable) initializer = none) :
    evalPanSemRecursiveCallFiniteContext (.dec name shape initializer body) context =
      some (some .error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hinit]

/-- HOL `evaluate_def` `Dec` clause: an initializer whose value does not match the
    declared shape yields the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_dec_shape_false {width : Nat} {σ : Type}
    [NeZero width]
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width)
    (context : FiniteEvalContext width σ) (value : ValueHOL width)
    (hinit : evalHOLFinite context.state (h := context.memaddrsDecidable) initializer =
      some value)
    (hshape : shapeEqHOL shape (shapeOfHOLExact value) = false) :
    evalPanSemRecursiveCallFiniteContext (.dec name shape initializer body) context =
      some (some .error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hinit]
  dsimp only
  rw [if_neg (by rw [hshape]; decide)]

/-- HOL `evaluate_def` `Dec` clause: once the initializer matches the shape, the
    recursive body result is restored by `res_var` on the local binding. -/
theorem evalPanSemRecursiveCallFiniteContext_dec_body_some {width : Nat} {σ : Type}
    [NeZero width]
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width)
    (context : FiniteEvalContext width σ) (value : ValueHOL width)
    (result : Option (PanSemResultExact width)) (postContext : FiniteEvalContext width σ)
    (hinit : evalHOLFinite context.state (h := context.memaddrsDecidable) initializer =
      some value)
    (hshape : shapeEqHOL shape (shapeOfHOLExact value) = true)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (context.withState (setVarHOLFinite name value context.state) rfl rfl) =
        some (result, postContext)) :
    evalPanSemRecursiveCallFiniteContext (.dec name shape initializer body) context =
      some (result, postContext.withState
        { postContext.state with
          locals := HolFiniteMapExact.resVarEq postContext.state.locals
            (name, context.state.locals.lookup name) } rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hinit]
  dsimp only
  rw [if_pos hshape]
  rw [hbody]

/-- HOL `evaluate_def` `While` clause: a zero-valued condition exits the loop with
    the `NONE` result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_while_word_zero {width : Nat} {σ : Type}
    [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width) (context : FiniteEvalContext width σ)
    (word : BitVec width)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word word)))
    (hzero : ¬ word ≠ 0) :
    evalPanSemRecursiveCallFiniteContext (.while condition body) context =
      some (none, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_neg hzero]

/-- HOL `evaluate_def` `While` clause: on an exhausted clock the loop returns
    `TimeOut` with emptied locals. -/
theorem evalPanSemRecursiveCallFiniteContext_while_clock_zero {width : Nat} {σ : Type}
    [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width) (context : FiniteEvalContext width σ)
    (word : BitVec width)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word word)))
    (hw : word ≠ 0) (hclock : context.state.clock = 0) :
    evalPanSemRecursiveCallFiniteContext (.while condition body) context =
      some (some .timeOut,
        context.withState (emptyLocalsHOLFinite context.state) rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_pos hw]
  rw [if_pos hclock]

/-- HOL `evaluate_def` `While` clause: a `Continue` (or `NONE`) body result
    re-enters the loop at the clock-fixed continuation state. -/
theorem evalPanSemRecursiveCallFiniteContext_while_body_continue {width : Nat} {σ : Type}
    [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width) (context : FiniteEvalContext width σ)
    (word : BitVec width) (bodyContext : FiniteEvalContext width σ)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word word)))
    (hw : word ≠ 0) (hclock : ¬ context.state.clock = 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (context.withState (decClockHOLFinite (width := width) (σ := σ) context.state) rfl rfl) =
        some (some PanSemResultExact.continue, bodyContext)) :
    evalPanSemRecursiveCallFiniteContext (.while condition body) context =
      evalPanSemRecursiveCallFiniteContext (.while condition body)
        (bodyContext.withState (fixClockHOLFinite (width := width) (σ := σ) (decClockHOLFinite (width := width) (σ := σ) context.state)
          ((some PanSemResultExact.continue, bodyContext.state) : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)).2 rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_pos hw]
  rw [if_neg hclock]
  rw [hbody]

/-- HOL `evaluate_def` `While` clause: a `Break` body result exits the loop with
    the `NONE` result at the clock-fixed continuation state. -/
theorem evalPanSemRecursiveCallFiniteContext_while_body_break {width : Nat} {σ : Type}
    [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width) (context : FiniteEvalContext width σ)
    (word : BitVec width) (bodyContext : FiniteEvalContext width σ)
    (hcond : evalHOLFinite context.state (h := context.memaddrsDecidable) condition =
      some (ValueHOL.val (HolWordLab.word word)))
    (hw : word ≠ 0) (hclock : ¬ context.state.clock = 0)
    (hbody : evalPanSemRecursiveCallFiniteContext body
      (context.withState (decClockHOLFinite (width := width) (σ := σ) context.state) rfl rfl) =
        some (some PanSemResultExact.break, bodyContext)) :
    evalPanSemRecursiveCallFiniteContext (.while condition body) context =
      some (none, bodyContext.withState (fixClockHOLFinite (width := width) (σ := σ) (decClockHOLFinite (width := width) (σ := σ) context.state)
        ((some PanSemResultExact.break, bodyContext.state) : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)).2 rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hcond]
  dsimp only
  rw [if_pos hw]
  rw [if_neg hclock]
  rw [hbody]

end PanSemStateFiniteExact

end Flapjack
