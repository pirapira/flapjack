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
`Skip` / `Break` / `Continue`, the `Seq` (three outcomes) and `If`
(then/else on a word condition) clauses, the `Dec` and `While` clauses, the
`Call` / `DecCall` argument-list and code-lookup short circuits plus the
clock-exhaustion (`TimeOut`, empty locals) branches, and the
`Return` / `Raise` / `ShMemLoad` / `ShMemStore` clauses.  The `Call` / `DecCall`
returned and exception outcome branches are still being added; the exact
`@[hol ... "evaluate_def" ...]` tag stays withheld until every clause is exposed
and reviewed (`flapjack-qj5` is blocked on `flapjack-6yq`).

The older delegating adapter `evaluateHOLFiniteViaExact` (and its
`evalPanSemRecursiveCallHOLFinite_of_broad` / `evaluateHOLFiniteViaExact_of_broad`
translation lemmas) remains as untagged Flapjack-specific infrastructure.

The module also carries the per-constructor projection equivalence to the broad
exact evaluator (`flapjack-6yq`): `..._skip_projection` / `_break_projection` /
`_continue_projection` / `_annot_projection` and the `assign` / `primitive` /
`store` / `store32` / `storeByte` / `extCall` / `tick` / `return` / `raise` /
`shMemLoad` / `shMemStore` projections show that mapping the finite evaluator's
result through `state.toExact` agrees with `...ContextHOLExact`.  The remaining
constructors (`dec` / `seq` / `ite` / `while` / `call` / `decCall`) are still to
come.
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

/-- HOL `evaluate_def` `Call` clause short circuit: an argument list that fails
    to evaluate yields the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_call_args_none {width : Nat} {σ : Type}
    [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (context : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments = none) :
    evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some PanSemResultExact.error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]

/-- HOL `evaluate_def` `Call` clause short circuit: a function whose code lookup
    fails yields the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_call_lookup_none {width : Nat} {σ : Type}
    [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (context : FiniteEvalContext width σ)
    (values : List (ValueHOL width))
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments =
      some values)
    (hlookupNone : lookupCodeHOLFinite context.state.code.lookup function values = none) :
    evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some PanSemResultExact.error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]
  dsimp only
  rw [hlookupNone]

/-- HOL `evaluate_def` `DecCall` clause short circuit: an argument list that fails
    to evaluate yields the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_args_none {width : Nat} {σ : Type}
    [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments = none) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (some PanSemResultExact.error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]

/-- HOL `evaluate_def` `DecCall` clause short circuit: a function whose code
    lookup fails yields the error result at the unchanged context. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_lookup_none {width : Nat} {σ : Type}
    [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ) (values : List (ValueHOL width))
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments =
      some values)
    (hlookupNone : lookupCodeHOLFinite context.state.code.lookup function values = none) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (some PanSemResultExact.error, context) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]
  dsimp only
  rw [hlookupNone]

/-- HOL `evaluate_def` `Call` clause clock-exhaustion branch: when the caller's
    clock is exhausted the call returns `TimeOut` with empty locals. -/
theorem evalPanSemRecursiveCallFiniteContext_call_clock_zero {width : Nat} {σ : Type}
    [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (context : FiniteEvalContext width σ)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments =
      some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock = 0) :
    evalPanSemRecursiveCallFiniteContext (.call info function arguments) context =
      some (some .timeOut, context.withState (emptyLocalsHOLFinite context.state) rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  rw [if_pos hclock]

/-- HOL `evaluate_def` `DecCall` clause clock-exhaustion branch: when the caller's
    clock is exhausted the call returns `TimeOut` with empty locals. -/
theorem evalPanSemRecursiveCallFiniteContext_decCall_clock_zero {width : Nat} {σ : Type}
    [NeZero width]
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL width)) (continuation : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (hargs : evalListHOLFinite context.state (h := context.memaddrsDecidable) arguments =
      some values)
    (hlookup : lookupCodeHOLFinite context.state.code.lookup function values =
      some (body, callee, returnShape))
    (hclock : context.state.clock = 0) :
    evalPanSemRecursiveCallFiniteContext
        (.decCall resultName shape function arguments continuation) context =
      some (some .timeOut, context.withState (emptyLocalsHOLFinite context.state) rfl rfl) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def]
  dsimp only
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  rw [if_pos hclock]

/-- Projection equivalence on `Skip`: mapping the finite evaluator's result
    through the canonical carrier projection `state.toExact` agrees with the
    broad exact evaluator on its (forgetful) projection.  First of the
    per-constructor projection-equivalence lemmas for `flapjack-6yq`. -/
theorem evalPanSemRecursiveCallFiniteContext_skip_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) :
    (evalPanSemRecursiveCallFiniteContext (.skip : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.skip : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp

/-- Projection equivalence on `Break` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_break_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) :
    (evalPanSemRecursiveCallFiniteContext (.break : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.break : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp

/-- Projection equivalence on `Continue` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_continue_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) :
    (evalPanSemRecursiveCallFiniteContext (.continue : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.continue : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp

/-- Projection equivalence on `Annot` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_annot_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (tag text : MlS) :
    (evalPanSemRecursiveCallFiniteContext (.annot tag text : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.annot tag text : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp


/-- Projection equivalence on `Assign` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_assign_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (kind : VarKind) (name : MlS)
    (value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.assign kind name value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.assign kind name value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `Primitive` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_primitive_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (name : MlS) (operator : PrimOp)
    (args : List (ExpHOL width)) :
    (evalPanSemRecursiveCallFiniteContext (.primitive name operator args : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.primitive name operator args : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `Store` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_store_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (address value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.store address value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.store address value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `Store32` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_store32_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (address value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.store32 address value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.store32 address value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `StoreByte` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_storeByte_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (address value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.storeByte address value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.storeByte address value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `ExtCall` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_extCall_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (function : MlS)
    (configuration configurationLength array arrayLength : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.extCall function configuration configurationLength array arrayLength : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.extCall function configuration configurationLength array arrayLength : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  simp only [evalPanSemNonrecursiveHOLFinite, evalPanSemNonrecursiveHOLExact]
  simp only [Option.map_some, FiniteEvalContext.withState_state,
    PanSemExactEvalContext.withState_state, toExact_ofExact]

/-- Projection equivalence on `Tick` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_tick_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) :
    (evalPanSemRecursiveCallFiniteContext (.tick : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.tick : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  dsimp only
  by_cases hclock : context.state.clock = 0
  · rw [if_pos hclock, if_pos hclock]
    rfl
  · rw [if_neg hclock, if_neg hclock]
    rfl

/-- Projection equivalence on `Return` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_return_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.return value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.return value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  dsimp only
  letI : DecidablePred context.state.memaddrs := context.memaddrsDecidable
  rw [← evalHOLFinite_eq_toExact context.state value]
  generalize hval : context.state.evalHOLFinite value = result
  cases result with
  | none => simp only [Option.map_some]
  | some returned =>
      simp only []
      by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.state.structs
          (shapeOfHOLExact returned) ≤ 32
      · rw [if_pos hsize, if_pos hsize]
        rfl
      · rw [if_neg hsize, if_neg hsize]
        rfl

/-- Projection equivalence on `Raise` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_raise_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (exception : MlS)
    (value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext (.raise exception value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact (.raise exception value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  dsimp only
  letI : DecidablePred context.state.memaddrs := context.memaddrsDecidable
  rw [← evalHOLFinite_eq_toExact context.state value]
  generalize hval : context.state.evalHOLFinite value = result
  cases result with
  | none => simp only [Option.map_some]
  | some raised =>
      simp only []
      cases hshape : context.state.eshapes.lookup exception with
      | none => simp only [Option.map_some]
      | some shape =>
          simp only []
          by_cases heq : shapeEqHOL (shapeOfHOLExact raised) shape
          · rw [if_pos heq, if_pos heq]
            by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.state.structs
                (shapeOfHOLExact raised) ≤ 32
            · rw [if_pos hsize, if_pos hsize]
              rfl
            · rw [if_neg hsize, if_neg hsize]
              rfl
          · rw [if_neg heq, if_neg heq]
            rfl

/-- Projection equivalence on `ShMemLoad` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_shMemLoad_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (size : OpSize)
    (kind : VarKind) (name : MlS) (address : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext
        (.shMemLoad size kind name address : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact
        (.shMemLoad size kind name address : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  dsimp only
  rfl

/-- Projection equivalence on `ShMemStore` (see `..._skip_projection`). -/
theorem evalPanSemRecursiveCallFiniteContext_shMemStore_projection {width : Nat} {σ : Type}
    [NeZero width] (context : FiniteEvalContext width σ) (size : OpSize)
    (address value : ExpHOL width) :
    (evalPanSemRecursiveCallFiniteContext
        (.shMemStore size address value : ProgHOL width) context).map
        (fun pair => (pair.1, pair.2.state.toExact)) =
      (evalPanSemRecursiveCallContextHOLExact
        (.shMemStore size address value : ProgHOL width)
        { state := context.state.toExact
          memaddrsDecidable := context.memaddrsDecidable
          shMemaddrsDecidable := context.shMemaddrsDecidable }).map
        (fun pair => (pair.1, pair.2.state)) := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_def,
    evalPanSemRecursiveCallContextHOLExact.eq_def]
  dsimp only
  rfl

/-- Projection equivalence on `Seq`, stated with projection hypotheses for the
    two recursive sub-calls so that it composes into the general induction.
    This is Flapjack-specific infrastructure; it is not a HOL declaration. -/
theorem evalPanSemRecursiveCallFiniteContext_seq_projection {width : Nat} {σ : Type}
    [NeZero width] (first second : ProgHOL width) (context : FiniteEvalContext width σ)
    (ihFirst : ∀ (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext first context = o →
        evalPanSemRecursiveCallContextHOLExact first context.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o)
    (ihSecond : ∀ (fc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext second fc = o →
        evalPanSemRecursiveCallContextHOLExact second fc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o) :
    Option.map (fun p => (p.1, p.2.toExact))
        (evalPanSemRecursiveCallFiniteContext (.seq first second) context) =
      evalPanSemRecursiveCallContextHOLExact (.seq first second) context.toExact := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_2,
    evalPanSemRecursiveCallContextHOLExact.eq_2]
  cases hfin : evalPanSemRecursiveCallFiniteContext first context with
  | none =>
      rw [ihFirst none hfin]
      simp only [Option.map_none]
  | some pair =>
      obtain ⟨firstResult, firstContext⟩ := pair
      rw [ihFirst (some (firstResult, firstContext)) hfin]
      simp only [Option.map_some]
      cases firstResult with
      | none =>
          simp only []
          rw [← ihSecond _ _ rfl]
          congr 1
      | some r =>
          simp only [Option.map_some]
          congr 1

/-- Alignment helper: `evalHOLExact` on `context.toExact` agrees with
    `evalHOLExact` on `context.state.toExact` (same instance).  Flapjack-specific. -/
theorem evalHOLExact_toExact_eq {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (expression : ExpHOL width) :
    @Flapjack.evalHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable
        expression =
      @Flapjack.evalHOLExact width σ _ context.state.toExact context.memaddrsDecidable
        expression :=
  rfl

/-- Argument-list alignment helper: `evalListHOLExact` on `context.toExact` agrees
    with `evalListHOLExact` on `context.state.toExact` (same instance).  Flapjack-specific. -/
theorem evalListHOLExact_toExact_eq {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ) (expressions : List (ExpHOL width)) :
    @Flapjack.evalListHOLExact width σ _ context.toExact.state context.toExact.memaddrsDecidable
        expressions =
      @Flapjack.evalListHOLExact width σ _ context.state.toExact context.memaddrsDecidable
        expressions :=
  rfl

/-- Projection-equivalence for the finite `Dec` clause against the broad exact
    evaluator, given the projection hypothesis for the recursive body.  Untagged
    Flapjack-specific support for the `evaluate_def` port. -/
theorem evalPanSemRecursiveCallFiniteContext_dec_projection {width : Nat} {σ : Type}
    [NeZero width] (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width)
    (body : ProgHOL width) (context : FiniteEvalContext width σ)
    (ihBody : ∀ (bc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext body bc = o →
        evalPanSemRecursiveCallContextHOLExact body bc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o) :
    Option.map (fun p => (p.1, p.2.toExact))
        (evalPanSemRecursiveCallFiniteContext (.dec name shape initializer body) context) =
      evalPanSemRecursiveCallContextHOLExact (.dec name shape initializer body) context.toExact := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_1, evalPanSemRecursiveCallContextHOLExact.eq_1]
  rw [evalHOLFinite_eq_toExact context.state (h := context.memaddrsDecidable) initializer]
  rw [evalHOLExact_toExact_eq context initializer]
  generalize hval : @Flapjack.evalHOLExact width σ _ context.state.toExact
      context.memaddrsDecidable initializer = result
  cases result with
  | none => rfl
  | some value =>
      simp only []
      by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value) = true
      · rw [if_pos hshape, if_pos hshape]
        generalize hbc : context.withState (setVarHOLFinite name value context.state) rfl rfl = bc
        generalize hbcb : context.toExact.withState
            (setVarHOLExact name value context.toExact.state) rfl rfl = bbc
        have hbbc : bbc = bc.toExact := by
          rw [← hbcb, ← hbc]
          apply PanSemExactEvalContext.ext
          change setVarHOLExact name value context.state.toExact =
            (setVarHOLFinite name value context.state).toExact
          rw [toExact_setVarHOLFinite]
        cases hbody : evalPanSemRecursiveCallFiniteContext body bc with
        | none => rw [hbbc, ihBody bc none hbody]; simp only [Option.map_none]
        | some pair =>
            obtain ⟨result, postContext⟩ := pair
            rw [hbbc, ihBody bc (some (result, postContext)) hbody]
            simp only [Option.map_some, Option.some.injEq]
            refine congrArg (fun c => (result, c)) ?_
            apply PanSemExactEvalContext.ext
            simp only [FiniteEvalContext.toExact, PanSemExactEvalContext.withState_state,
              FiniteEvalContext.withState_state, toExact_resVarEq_locals]
      · rw [if_neg hshape, if_neg hshape]; rfl

/-- The `If` clause recurses on the same context, so its projection follows
    directly from the two branch IHs.  Flapjack-specific. -/
theorem evalPanSemRecursiveCallFiniteContext_ite_projection {width : Nat} {σ : Type}
    [NeZero width] (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (ihThen : ∀ (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext thenBranch context = o →
        evalPanSemRecursiveCallContextHOLExact thenBranch context.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o)
    (ihElse : ∀ (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext elseBranch context = o →
        evalPanSemRecursiveCallContextHOLExact elseBranch context.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o) :
    Option.map (fun p => (p.1, p.2.toExact))
        (evalPanSemRecursiveCallFiniteContext (.ite condition thenBranch elseBranch) context) =
      evalPanSemRecursiveCallContextHOLExact (.ite condition thenBranch elseBranch) context.toExact := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_3, evalPanSemRecursiveCallContextHOLExact.eq_3]
  rw [evalHOLFinite_eq_toExact context.state (h := context.memaddrsDecidable) condition]
  rw [evalHOLExact_toExact_eq context condition]
  generalize hcond : @Flapjack.evalHOLExact width σ _ context.state.toExact
      context.memaddrsDecidable condition = result
  cases result with
  | none => rfl
  | some v =>
      cases v with
      | val wordLab =>
          cases wordLab with
          | word value =>
              simp only []
              by_cases hz : (value != 0) = true
              · rw [if_pos hz, if_pos hz]
                exact (ihThen (evalPanSemRecursiveCallFiniteContext thenBranch context) rfl).symm
              · rw [if_neg hz, if_neg hz]
                exact (ihElse (evalPanSemRecursiveCallFiniteContext elseBranch context) rfl).symm
      | rStruct fields => rfl
      | nStruct name fields => rfl

/-- Projection equivalence for the `While` clause, using a body IH and a self IH. -/
theorem evalPanSemRecursiveCallFiniteContext_while_projection {width : Nat} {σ : Type}
    [NeZero width] (condition : ExpHOL width) (body : ProgHOL width)
    (context : FiniteEvalContext width σ)
    (ihBody : ∀ (fc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext body fc = o →
        evalPanSemRecursiveCallContextHOLExact body fc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o)
    (ihSelf : ∀ (fc : FiniteEvalContext width σ)
        (o : Option (Option (PanSemResultExact width) × FiniteEvalContext width σ)),
        evalPanSemRecursiveCallFiniteContext (.while condition body) fc = o →
        evalPanSemRecursiveCallContextHOLExact (.while condition body) fc.toExact =
          Option.map (fun p => (p.1, p.2.toExact)) o) :
    Option.map (fun p => (p.1, p.2.toExact))
        (evalPanSemRecursiveCallFiniteContext (.while condition body) context) =
      evalPanSemRecursiveCallContextHOLExact (.while condition body) context.toExact := by
  rw [evalPanSemRecursiveCallFiniteContext.eq_4, evalPanSemRecursiveCallContextHOLExact.eq_4]
  rw [evalHOLFinite_eq_toExact context.state (h := context.memaddrsDecidable) condition]
  rw [evalHOLExact_toExact_eq context condition]
  generalize hcond : @Flapjack.evalHOLExact width σ _ context.state.toExact
      context.memaddrsDecidable condition = result
  cases result with
  | none => rfl
  | some v =>
      cases v with
      | val wordLab =>
          cases wordLab with
          | word word =>
              simp only []
              by_cases hw : word ≠ 0
              · rw [if_pos hw, if_pos hw]
                by_cases hclock : context.state.clock = 0
                · have hclock' : context.toExact.state.clock = 0 := hclock
                  rw [if_pos hclock, if_pos hclock']
                  simp only [Option.map_some, Option.some.injEq]
                  have hb : (context.withState (emptyLocalsHOLFinite context.state) rfl rfl).toExact =
                      context.toExact.withState (emptyLocalsHOLExact context.toExact.state) rfl rfl := by
                    apply PanSemExactEvalContext.ext
                    change emptyLocalsHOLExact context.state.toExact =
                      (emptyLocalsHOLFinite context.state).toExact
                    rw [toExact_emptyLocalsHOLFinite]
                  rw [hb]
                · have hclock' : ¬(context.toExact.state.clock = 0) := hclock
                  rw [if_neg hclock, if_neg hclock']
                  generalize hent : context.withState (decClockHOLFinite context.state) rfl rfl = ent
                  generalize hentb : context.toExact.withState
                      (decClockHOLExact context.toExact.state) rfl rfl = entb
                  have hentb_eq : entb = ent.toExact := by
                    rw [← hentb, ← hent]
                    apply PanSemExactEvalContext.ext
                    change decClockHOLExact context.state.toExact =
                      (decClockHOLFinite context.state).toExact
                    rw [toExact_decClockHOLFinite]
                  rw [hentb_eq]
                  cases hbody : evalPanSemRecursiveCallFiniteContext body ent with
                  | none => rw [ihBody ent none hbody]; simp only [Option.map_none]
                  | some pair =>
                      obtain ⟨bodyResult, bodyContext⟩ := pair
                      rw [ihBody ent (some (bodyResult, bodyContext)) hbody]
                      simp only [Option.map_some]
                      cases bodyResult with
                      | none => rw [← ihSelf _ _ rfl]; congr 1
                      | some r =>
                          cases r with
                          | «continue» => rw [← ihSelf _ _ rfl]; congr 1
                          | «break» => congr 1
                          | _ => congr 1
              · rw [if_neg hw, if_neg hw]; rfl
      | rStruct fields => rfl
      | nStruct name fields => rfl

end PanSemStateFiniteExact

end Flapjack
