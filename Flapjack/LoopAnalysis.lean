import Flapjack.CrepToLoop
import Flapjack.LoopCall

/-!
Structural analyses for the Loop language. These are the list-based
counterparts of CakeML's `loop_live` inputs; a later pass can replace the
lists with a finite-set representation without changing the syntax layer.
-/

namespace Flapjack

def loopVarsOfExp : LoopExp α → List Nat
  | .const _ => []
  | .var name => [name]
  | .lookup _ => []
  | .load address => loopVarsOfExp address
  | .op _ arguments => arguments.flatMap loopVarsOfExp
  | .crepOp _ arguments => arguments.flatMap loopVarsOfExp
  | .cmp _ left right => loopVarsOfExp left ++ loopVarsOfExp right
  | .shift _ left right => loopVarsOfExp left ++ loopVarsOfExp right
  | .baseAddr => []
  | .topAddr => []

/-! Source-shaped port of `loop_live$vars_of_exp`
    (`cakeml/pancake/loop_liveScript.sml:11`).  HOL carries the live names as
    a canonical `num_set`; the Lean syntax layer keeps lists, so fold the
    expression reads into the existing sorted insertion helper. -/
def varsOfExp (expression : LoopExp α) (live : List Nat) : List Nat :=
  (loopVarsOfExp expression).foldr insertNatSorted live

def deleteNatSorted (name : Nat) : List Nat → List Nat
  | [] => []
  | head :: tail =>
      if name == head then deleteNatSorted name tail
      else head :: deleteNatSorted name tail

/-! Source-shaped port of `loop_live$arith_vars`
    (`cakeml/pancake/loop_liveScript.sml:50`). -/
def arithVars : LoopArith → List Nat → List Nat
  | .longMul destinationLeft destinationRight sourceLeft sourceRight, live =>
      insertNatSorted sourceLeft
        (insertNatSorted sourceRight
          (deleteNatSorted destinationLeft
            (deleteNatSorted destinationRight live)))
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient, live =>
      insertNatSorted sourceLeft
        (insertNatSorted sourceRight
          (insertNatSorted quotient
            (deleteNatSorted destinationLeft
              (deleteNatSorted destinationRight live))))
  | .div destination dividend divisor, live =>
      insertNatSorted dividend
        (insertNatSorted divisor (deleteNatSorted destination live))

def loopListDeleteSorted (names : List Nat) (live : List Nat) : List Nat :=
  names.foldl (fun current name => deleteNatSorted name current) live

def loopIntersectSorted (left right : List Nat) : List Nat :=
  left.filter (fun name => name ∈ right)

/-! Cake's fixedpoint grows only within `liveIn`, so at most one strict growth
    step is possible for each live name before the final stabilization check. -/
def loopFixedpointFuel (liveIn : List Nat) : Nat :=
  liveIn.length + 1

/-! The `Call` equations of CakeML's `loop_live$shrink` use the arguments as
    reads and restrict a call's returned live set to the variables live after
    the call.  Keeping this as a separate helper makes the source equation
    visible at the executable boundary.  This helper is the exact no-handler
    equation from `cakeml/pancake/loop_liveScript.sml:116-123`; the handler
    branch below applies the same equation to its two child programs. -/
def loopShrinkCallNoHandler (returns : Option (List Nat × List Nat))
    (target : Option Nat) (arguments : List Nat) (live : List Nat) :
    LoopProg α × List Nat :=
  match returns with
  | none =>
      (.call none target arguments none, loopListInsert arguments live)
  | some (names, liveOut) =>
      let callLive := loopListDeleteSorted names (loopIntersectSorted live liveOut)
      (.call (some (names, callLive)) target arguments none,
        loopListInsert arguments callLive)

def loopContextAt : Nat → List (List Nat × List Nat) → Option (List Nat × List Nat)
  | _, [] => none
  | 0, context :: _ => some context
  | fuel + 1, _ :: contexts => loopContextAt fuel contexts

/-! Source-shaped leaf and structured equations from `loop_live$shrink`
    (`cakeml/pancake/loop_liveScript.sml:62`).  Ordinary loops use the
    source's bounded fixed-point equation below; the loop context used by
    `break`/`continue` remains a refinement boundary.  All other equations
    are executable here with list-backed num_sets. -/
def loopShrinkLeaf : LoopProg α → List Nat → LoopProg α × List Nat
  | .skip, live => (.skip, live)
  | .assign name value, live =>
      if name ∈ live then
        (.assign name value, varsOfExp value (deleteNatSorted name live))
      else
        (.skip, live)
  | .primitive destinations operator arguments, live =>
      (.primitive destinations operator arguments,
        loopListInsert arguments (loopListDeleteSorted destinations live))
  | .arith operation, live => (.arith operation, arithVars operation live)
  | .store address value, live =>
      (.store address value, varsOfExp address (insertNatSorted value live))
  | .setGlobal address value, live =>
      (.setGlobal address value, varsOfExp value live)
  | .load32 address destination, live =>
      (.load32 address destination,
        insertNatSorted address (deleteNatSorted destination live))
  | .loadByte address destination, live =>
      (.loadByte address destination,
        insertNatSorted address (deleteNatSorted destination live))
  | .store32 address value, live =>
      (.store32 address value,
        insertNatSorted address (insertNatSorted value live))
  | .storeByte address value, live =>
      (.storeByte address value,
        insertNatSorted address (insertNatSorted value live))
  | .seq first second, live =>
      let (second', live') := loopShrinkLeaf second live
      let (first', live'') := loopShrinkLeaf first live'
      (.seq first' second', live'')
  | .ite operator condition right thenBranch elseBranch branchLive, live =>
      let restricted := loopIntersectSorted branchLive live
      let (then', thenLive) := loopShrinkLeaf thenBranch restricted
      let (else', elseLive) := loopShrinkLeaf elseBranch restricted
      let rightLive := match right with
        | .reg name => [name]
        | .imm _ => []
      /- CakeML's `shrink` shrinks all cutsets, including the `If` one:
         the emitted `If` carries `inter l l1`, not the original set
         (`loop_liveScript.sml:75-80`). -/
      (.ite operator condition right then' else' restricted,
        insertNatSorted condition
          (loopListInsert rightLive (loopListUnion thenLive elseLive)))
  | .break label, _ => (.break label, [])
  | .continue label, _ => (.continue label, [])
  | .fail, _ => (.fail, [])
  | .return values, _ => (.return values, loopListInsert values [])
  | .raise exception, _ => (.raise exception, [exception])
  | .shMem operator name address, live =>
      (.shMem operator name address,
        varsOfExp address (insertNatSorted name live))
  | .tick, live => (.tick, live)
  | .mark body, live =>
      let (body', live') := loopShrinkLeaf body live
      (.mark body', live')
  | .locValue destination source, live =>
      if destination ∈ live then
        (.locValue destination source, deleteNatSorted destination live)
      else
        (.skip, live)
  | .ffi function configuration configurationLength array arrayLength liveOut, live =>
      let restricted := loopIntersectSorted liveOut live
      (.ffi function configuration configurationLength array arrayLength restricted,
        loopListInsert [configuration, configurationLength, array, arrayLength] restricted)
  | .loop liveIn body liveOut, live =>
      let loopLiveOut := loopIntersectSorted liveOut live
      let bodyEntryLive := loopListInsert liveIn loopLiveOut
      /- Cake's `fixedpoint` repeats the body shrink with `bex`, the union of
         the loop's live-in and output sets, until the live-in set stabilizes.
         The bound is an
         executable representation of the finite-set decrease argument used
         by the HOL definition; Pancake live sets are bounded by the source
         program, so this comfortably covers generated bodies. -/
      let rec fixedpoint (fuel : Nat) (previous : List Nat) :
          LoopProg α × List Nat :=
        match fuel with
        | 0 =>
            let (fallback, _) := loopShrinkLeaf body bodyEntryLive
            (.loop liveIn fallback loopLiveOut, liveIn)
        | fuel + 1 =>
            let (body', bodyLive) := loopShrinkLeaf body bodyEntryLive
            let current := loopIntersectSorted liveIn bodyLive
            if current = previous then
              (.loop current body' loopLiveOut, current)
            else if current.length ≤ previous.length then
              let (fallback, _) := loopShrinkLeaf body bodyEntryLive
              (.loop liveIn fallback loopLiveOut, liveIn)
            else
              fixedpoint fuel current
      fixedpoint (loopFixedpointFuel liveIn) []
  | .call returns target arguments none, live =>
      loopShrinkCallNoHandler returns target arguments live
  | .call returns target arguments
      (some (exception, handler, normal, handlerLiveOut)), live =>
      let (normal', normalLive) := loopShrinkLeaf normal live
      let (handler', handlerLive) := loopShrinkLeaf handler live
      let returnLive := match returns with
        | none => []
        | some (names, liveOut) =>
            loopIntersectSorted liveOut
              (loopListInsert (loopListDeleteSorted names normalLive)
                (deleteNatSorted exception handlerLive))
      (.call (returns.map (fun (names, _) => (names, returnLive))) target
          arguments
          (some (exception, handler', normal',
            loopIntersectSorted live handlerLiveOut)),
        loopListInsert arguments returnLive)

/-! Context-aware port of the structured part of `loop_live$shrink`.  The
    context is stored outermost-first, so label `0` denotes the innermost
    loop, matching HOL's `oEL` lookup.  Leaf equations are shared with
    `loopShrinkLeaf`; structured nodes recurse here so calls in handlers and
    loop bodies see the same break/continue context as the source. -/
mutual
def loopShrink (contexts : List (List Nat × List Nat)) :
    LoopProg α → List Nat → LoopProg α × List Nat
  | .seq first second, live =>
      let (second', live') := loopShrink contexts second live
      let (first', live'') := loopShrink contexts first live'
      (.seq first' second', live'')
  | .ite operator condition right thenBranch elseBranch branchLive, live =>
      let restricted := loopIntersectSorted branchLive live
      let (then', thenLive) := loopShrink contexts thenBranch restricted
      let (else', elseLive) := loopShrink contexts elseBranch restricted
      let rightLive := match right with
        | .reg name => [name]
        | .imm _ => []
      /- CakeML's `shrink` shrinks all cutsets, including the `If` one:
         the emitted `If` carries `inter l l1`, not the original set
         (`loop_liveScript.sml:75-80`). -/
      (.ite operator condition right then' else' restricted,
        insertNatSorted condition
          (loopListInsert rightLive (loopListUnion thenLive elseLive)))
  | .mark body, live => loopShrink contexts body live
  | .break label, _ =>
      (.break label, (loopContextAt label contexts).map Prod.snd |>.getD [])
  | .continue label, _ =>
      (.continue label, (loopContextAt label contexts).map Prod.fst |>.getD [])
  | .loop liveIn body liveOut, live =>
      let loopLiveOut := loopIntersectSorted liveOut live
      let bodyEntryLive := loopListInsert liveIn loopLiveOut
      match loopShrinkFixed contexts liveIn body loopLiveOut bodyEntryLive
          (loopFixedpointFuel liveIn) [] with
      | some result => result
      | none =>
          let (body', _) := loopShrink ((liveIn, loopLiveOut) :: contexts)
            body bodyEntryLive
          (.loop liveIn body' loopLiveOut, liveIn)
  | .call none target arguments none, live =>
      loopShrinkCallNoHandler none target arguments live
  | .call (some (names, liveOut)) target arguments none, live =>
      loopShrinkCallNoHandler (some (names, liveOut)) target arguments live
  | .call returns target arguments
      (some (exception, handler, normal, handlerLiveOut)), live =>
      match returns with
      | none => loopShrinkCallNoHandler none target arguments live
      | some (names, liveOut) =>
          let (normal', normalLive) := loopShrink contexts normal live
          let (handler', handlerLive) := loopShrink contexts handler live
          let returnLive := loopIntersectSorted liveOut
            (loopListInsert (loopListDeleteSorted names normalLive)
              (deleteNatSorted exception handlerLive))
          (.call (some (names, returnLive)) target arguments
              (some (exception, handler', normal',
                loopIntersectSorted live handlerLiveOut)),
            loopListInsert arguments returnLive)
  | program, live => loopShrinkLeaf program live

termination_by program => (sizeOf program, 0)

def loopShrinkFixed (contexts : List (List Nat × List Nat))
    (liveIn : List Nat) (body : LoopProg α)
    (loopLiveOut bodyEntryLive : List Nat) :
    Nat → List Nat → Option (LoopProg α × List Nat)
  | 0, _ => none
  | fuel + 1, previous =>
      /- `fixedpoint` passes its `bex` argument to every body shrink; using
         only `loopLiveOut` drops assignments that are needed to establish
         the loop's incoming cutset (loop_liveScript.sml:67-78). -/
      let (body', bodyLive) := loopShrink
        ((loopIntersectSorted liveIn previous, bodyEntryLive) :: contexts)
        body bodyEntryLive
      let current := loopIntersectSorted liveIn bodyLive
      if current = previous then
        some (.loop current body' loopLiveOut, current)
      else if current.length ≤ previous.length then
        none
      else
        loopShrinkFixed contexts liveIn body loopLiveOut bodyEntryLive fuel current
  termination_by fuel _ => (sizeOf body, fuel)
end

/-! Faithful executable port of `loop_live$mark_all` from
    `cakeml/pancake/loop_liveScript.sml:189`.  The Boolean records whether
    the source marked the whole node; the recursive calls preserve the
    intermediate marked children before rebuilding each parent. -/
def loopMarkAll : LoopProg α → LoopProg α × Bool
  | .seq first second =>
      let (first', firstMarked) := loopMarkAll first
      let (second', secondMarked) := loopMarkAll second
      let marked := firstMarked && secondMarked
      (if marked then .mark (.seq first' second') else .seq first' second', marked)
  | .loop liveIn body liveOut =>
      let (body', _) := loopMarkAll body
      (.loop liveIn body' liveOut, false)
  | .ite operator condition right thenBranch elseBranch live =>
      let (then', thenMarked) := loopMarkAll thenBranch
      let (else', elseMarked) := loopMarkAll elseBranch
      let marked := thenMarked && elseMarked
      let program := .ite operator condition right then' else' live
      (if marked then .mark program else program, marked)
  | .mark body => loopMarkAll body
  | .call returns target arguments .none =>
      (.mark (.call returns target arguments .none), true)
  | .call returns target arguments
      (.some (exception, handler, normal, liveOut)) =>
      let (handler', handlerMarked) := loopMarkAll handler
      let (normal', normalMarked) := loopMarkAll normal
      let marked := handlerMarked && normalMarked
      let program :=
        .call returns target arguments
          (.some (exception, handler', normal', liveOut))
      (if marked then .mark program else program, marked)
  | program => (.mark program, true)

/-! Source-shaped composition for `loop_live$comp` from
    `cakeml/pancake/loop_liveScript.sml:217`.  The list-backed executable
    shrink pass is seeded with the empty live set, then the marked program is
    projected exactly as the HOL `FST (mark_all (FST (shrink ...)))` equation. -/
def loopLiveComp (program : LoopProg α) : LoopProg α :=
  (loopMarkAll (loopShrink [] program []).1).1

/-! Source-shaped composition for `loop_live$optimise` from
    `cakeml/pancake/loop_liveScript.sml:221`.  `loop_call$comp` runs first
    with the empty location environment; its compiled program is then passed
    through the liveness composition above. -/
def loopLiveOptimise (program : LoopProg α) : LoopProg α :=
  loopLiveComp (LoopCall.comp [] program).1

/-! Faithful port of CakeML Pancake's `locals_touched_def` from
    `cakeml/pancake/loopLangScript.sml:77`.  The source definition is used on
    the original Loop expressions, before the later Flapjack-only `crepOp` and
    comparison expression forms are introduced; those forms are nevertheless
    handled structurally here so the analysis remains total on `LoopExp`. -/
def loopLocalsTouched : LoopExp α → List Nat
  | .const _ => []
  | .var name => [name]
  | .lookup _ => []
  | .load address => loopLocalsTouched address
  | .op _ arguments => arguments.flatMap loopLocalsTouched
  | .crepOp _ arguments => arguments.flatMap loopLocalsTouched
  | .cmp _ left right => loopLocalsTouched left ++ loopLocalsTouched right
  | .shift _ left right => loopLocalsTouched left ++ loopLocalsTouched right
  | .baseAddr => []
  | .topAddr => []

@[simp] theorem loopLocalsTouched_const (value : α) :
    loopLocalsTouched (.const value) = [] := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_var (α : Type u) (name : Nat) :
    loopLocalsTouched (α := α) (.var name) = [name] := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_lookup (address : α) :
    loopLocalsTouched (.lookup address) = [] := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_load (address : LoopExp α) :
    loopLocalsTouched (.load address) = loopLocalsTouched address := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_op (operator : BinOp)
    (arguments : List (LoopExp α)) :
    loopLocalsTouched (.op operator arguments) =
      arguments.flatMap loopLocalsTouched := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_shift (operator : Shift)
    (left right : LoopExp α) :
    loopLocalsTouched (.shift operator left right) =
      loopLocalsTouched left ++ loopLocalsTouched right := by
  simp [loopLocalsTouched]

def loopAssignedVars : LoopProg α → List Nat
  | .skip => []
  | .assign name _ => [name]
  | .primitive destinations _ _ => destinations
  | .arith operation =>
      match operation with
      | .longMul left right _ _ => [left, right]
      | .longDiv left right _ _ _ => [left, right]
      | .div destination _ _ => [destination]
  | .load32 _ destination => [destination]
  | .loadByte _ destination => [destination]
  | .seq first second => loopAssignedVars first ++ loopAssignedVars second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopAssignedVars thenBranch ++ loopAssignedVars elseBranch
  | .locValue destination _ => [destination]
  | .shMem _ destination _ => [destination]
  | .mark body => loopAssignedVars body
  | .loop _ body _ => loopAssignedVars body
  | .call none _ _ _ => []
  | .call (some (returns, _)) _ _ none => returns
  | .call (some (returns, _)) _ _ (some (exception, handler, normal, _)) =>
      returns ++ exception :: loopAssignedVars handler ++ loopAssignedVars normal
  | _ => []

def loopInsert (name : Nat) (names : List Nat) : List Nat :=
  if name ∈ names then names else name :: names

def loopInsertAll : List Nat → List Nat → List Nat
  | [], names => names
  | name :: rest, names => loopInsert name (loopInsertAll rest names)

theorem loopInsert_nodup (name : Nat) (names : List Nat)
    (hnames : names.Nodup) : (loopInsert name names).Nodup := by
  by_cases hname : name ∈ names
  · simp [loopInsert, hname, hnames]
  · simp [loopInsert, hname, hnames]

theorem loopInsertAll_nodup (added names : List Nat)
    (hnames : names.Nodup) : (loopInsertAll added names).Nodup := by
  induction added generalizing names with
  | nil => exact hnames
  | cons name rest ih =>
      exact loopInsert_nodup name (loopInsertAll rest names)
        (ih names hnames)

def loopAccVars : LoopProg α → List Nat → List Nat
  | .seq first second, names => loopAccVars first (loopAccVars second names)
  | .break _, names => names
  | .continue _, names => names
  | .loop _ body _, names => loopAccVars body names
  | .ite _ _ _ thenBranch elseBranch _, names =>
      /- `loopLang$acc_vars` intentionally records assigned variables only;
         condition operands are reads and are not part of the dense
         `loop_to_word` context.  In particular, do not include the
         condition or register operand here (`loopLangScript.sml:123`). -/
      loopAccVars thenBranch (loopAccVars elseBranch names)
  | .arith operation, names =>
      match operation with
      | .longMul left right _ _ => loopInsertAll [left, right] names
      | .longDiv left right _ _ _ => loopInsertAll [left, right] names
      | .div destination _ _ => loopInsert destination names
  | .mark body, names => loopAccVars body names
  | .tick, names => names
  | .skip, names => names
  | .fail, names => names
  | .raise _, names => names
  | .return _, names => names
  | .call none _ _ _, names => names
  | .call (some (returns, _)) _ _ none, names =>
      loopInsertAll returns names
  | .call (some (returns, _)) _ _
      (some (exception, handler, normal, _)), names =>
      let names := loopAccVars handler (loopAccVars normal names)
      loopInsert exception (loopInsertAll returns names)
  | .locValue destination _label, names => loopInsert destination names
  | .assign destination _, names => loopInsert destination names
  | .primitive destinations _ _, names => loopInsertAll destinations names
  | .shMem _ destination _, names => loopInsert destination names
  | .store _ _, names => names
  | .setGlobal _ _, names => names
  | .load32 _ destination, names => loopInsert destination names
  | .loadByte _ destination, names => loopInsert destination names
  | .store32 _ _, names => names
  | .storeByte _ _, names => names
  | .ffi _ _ _ _ _ _, names => names

theorem loopVarsOfExp_load (address : LoopExp α) :
    loopVarsOfExp (.load address) = loopVarsOfExp address := by
  simp [loopVarsOfExp]

theorem loopAssignedVars_seq (first second : LoopProg α) :
    loopAssignedVars (.seq first second) =
      loopAssignedVars first ++ loopAssignedVars second := by
  simp [loopAssignedVars]

theorem loopAccVars_skip (names : List Nat) :
    loopAccVars (.skip : LoopProg α) names = names := by
  rfl

/-! Cake `crep_to_loopProofScript.sml:355` `assigned_vars_MAPi_Assign`:
    a nested sequence of assignments to `offset, …, offset + count - 1`
    assigns exactly those variables.  `loopAssignNames` is the Flapjack
    counterpart of Cake's `MAPi (λn. Assign (n + offset))`. -/

theorem loopAssignedVars_nestedSeq (statements : List (LoopProg α)) :
    loopAssignedVars (loopNestedSeq statements) =
      statements.flatMap loopAssignedVars := by
  induction statements with
  | nil => simp [loopNestedSeq, loopAssignedVars]
  | cons statement statements ih =>
      simp [loopNestedSeq, loopAssignedVars_seq, ih]

/-- Cake's `assigned_vars_nested_seq_split`
    (`cakeml/pancake/semantics/loopPropsScript.sml:880`): the variables
    assigned by a nested sequence of two statement lists is the concatenation
    of the two lists' assigned variables. -/
theorem loopAssignedVars_nestedSeq_append (statements rest : List (LoopProg α)) :
    loopAssignedVars (loopNestedSeq (statements ++ rest)) =
      loopAssignedVars (loopNestedSeq statements) ++
        loopAssignedVars (loopNestedSeq rest) := by
  rw [loopAssignedVars_nestedSeq, loopAssignedVars_nestedSeq,
    loopAssignedVars_nestedSeq, List.flatMap_append]

def loopAssignNames (names : List Nat) (expression : LoopExp α) :
    List (LoopProg α) :=
  names.map (fun name => .assign name expression)

theorem loopAssignNames_cons (name : Nat) (names : List Nat)
    (expression : LoopExp α) :
    loopAssignNames (name :: names) expression =
      .assign name expression :: loopAssignNames names expression := by
  simp [loopAssignNames]

theorem loopAssignedVars_loopAssignNames (names : List Nat)
    (expression : LoopExp α) :
    loopAssignedVars (loopNestedSeq (loopAssignNames names expression)) =
      names := by
  rw [loopAssignedVars_nestedSeq]
  induction names with
  | nil => simp [loopAssignNames]
  | cons name names ih =>
      rw [loopAssignNames_cons]
      simp only [List.flatMap_cons]
      rw [loopAssignedVars, ih]
      rfl

/-- Cake `crep_to_loopProofScript.sml:355` `assigned_vars_MAPi_Assign`, stated
    for the `loopTempNames offset count` numbering produced by the executable
    inliner. -/
theorem loopAssignedVars_loopTempNames (offset count : Nat)
    (expression : LoopExp α) :
    loopAssignedVars
        (loopNestedSeq (loopAssignNames (loopTempNames offset count) expression)) =
      loopTempNames offset count :=
  loopAssignedVars_loopAssignNames _ _

def loopAssignPairs (names : List Nat) (expressions : List (LoopExp α)) :
    List (LoopProg α) :=
  names.zipWith (fun name expression => .assign name expression) expressions

theorem loopAssignPairs_cons (name : Nat) (names : List Nat)
    (expression : LoopExp α) (expressions : List (LoopExp α)) :
    loopAssignPairs (name :: names) (expression :: expressions) =
      .assign name expression :: loopAssignPairs names expressions := by
  simp [loopAssignPairs]

theorem loopAssignedVars_loopAssignPairs (names : List Nat)
    (expressions : List (LoopExp α)) (hlen : names.length = expressions.length) :
    loopAssignedVars (loopNestedSeq (loopAssignPairs names expressions)) =
      names := by
  induction names generalizing expressions with
  | nil =>
      cases expressions with
      | nil => simp [loopAssignPairs, loopNestedSeq, loopAssignedVars]
      | cons expression expressions => simp at hlen
  | cons name names ih =>
      cases expressions with
      | nil => simp at hlen
      | cons expression expressions =>
          rw [loopAssignPairs_cons, loopAssignedVars_nestedSeq]
          simp only [List.flatMap_cons, loopAssignedVars]
          rw [← loopAssignedVars_nestedSeq (loopAssignPairs names expressions)]
          rw [ih expressions (by simpa using hlen)]
          rfl

/-! Cake `loopPropsScript.sml:40` `cut_sets_def`: the list-backed live set
    after executing a Loop statement.  Cake's HOL `insert`/`num_set` is
    replaced by the sorted-list `insertNatSorted`, matching the rest of the
    Flapjack live-set layer. -/

def loopCutSets (live : List Nat) : LoopProg α → List Nat
  | .skip => live
  | .locValue destination _ => insertNatSorted destination live
  | .assign name _ => insertNatSorted name live
  | .load32 _ destination => insertNatSorted destination live
  | .loadByte _ destination => insertNatSorted destination live
  | .seq first second => loopCutSets (loopCutSets live first) second
  | .ite _ _ _ _ _ live' => live'
  | .arith (.longMul destinationLeft destinationRight _ _) =>
      insertNatSorted destinationLeft (insertNatSorted destinationRight live)
  | .arith (.longDiv destinationLeft destinationRight _ _ _) =>
      insertNatSorted destinationLeft (insertNatSorted destinationRight live)
  | .arith (.div destination _ _) => insertNatSorted destination live
  | _ => live

/-- Cake `crep_to_loopProofScript.sml:342` `cut_sets_MAPi_Assign`: running the
    assignments produced for `offset, …, offset + count - 1` adds exactly
    those names to the live set. -/
theorem loopCutSets_loopAssignPairs (live : List Nat) (names : List Nat)
    (expressions : List (LoopExp α)) (hlen : names.length = expressions.length) :
    loopCutSets live (loopNestedSeq (loopAssignPairs names expressions)) =
      loopListInsert names live := by
  induction names generalizing expressions live with
  | nil =>
      cases expressions with
      | nil => simp [loopAssignPairs, loopNestedSeq, loopCutSets, loopListInsert]
      | cons expression expressions => simp at hlen
  | cons name names ih =>
      cases expressions with
      | nil => simp at hlen
      | cons expression expressions =>
          simp only [loopAssignPairs_cons, loopNestedSeq, loopCutSets, loopListInsert]
          exact ih (insertNatSorted name live) expressions (by simpa using hlen)

/-- Cake `crep_to_loopProofScript.sml:342`, stated for the `loopTempNames`
    numbering produced by the executable inliner. -/
theorem loopCutSets_loopTempNames (live : List Nat) (offset count : Nat)
    (expressions : List (LoopExp α))
    (hlen : (loopTempNames offset count).length = expressions.length) :
    loopCutSets live
        (loopNestedSeq (loopAssignPairs (loopTempNames offset count) expressions)) =
      loopListInsert (loopTempNames offset count) live :=
  loopCutSets_loopAssignPairs live _ expressions hlen

/-- Cake's `cut_sets_nested_seq`
    (`cakeml/pancake/semantics/loopPropsScript.sml:767`): cutting a nested
    sequence of two statement lists is cutting the first and then the second. -/
theorem loopCutSets_nestedSeq_append (live : List Nat)
    (statements rest : List (LoopProg α)) :
    loopCutSets live (loopNestedSeq (statements ++ rest)) =
      loopCutSets (loopCutSets live (loopNestedSeq statements))
        (loopNestedSeq rest) := by
  induction statements generalizing live with
  | nil => simp [loopNestedSeq, loopCutSets]
  | cons statement statements ih =>
      simp only [List.cons_append, loopNestedSeq, loopCutSets]
      rw [ih (loopCutSets live statement)]

/-- Counterpart of Cake `survives_def` (`cakeml/pancake/semantics/loopPropsScript.sml:25`):
    a variable survives a Loop program when every control-flow path that can
    reach a use of it keeps it live.  Flapjack's live sets are plain lists, so
    Cake's `n ∈ domain cs` becomes list membership. -/
def loopSurvives (name : Nat) : LoopProg α → Prop
  | .ite _ _ _ thenBranch elseBranch live =>
      loopSurvives name thenBranch ∧ loopSurvives name elseBranch ∧ name ∈ live
  | .loop liveIn body liveOut =>
      name ∈ liveIn ∧ name ∈ liveOut ∧ loopSurvives name body
  | .call (some (_, cs)) _ _ none => name ∈ cs
  | .call (some (_, cs)) _ _ (some (_, first, second, ps)) =>
      name ∈ cs ∧ name ∈ ps ∧ loopSurvives name first ∧ loopSurvives name second
  | .ffi _ _ _ _ _ live => name ∈ live
  | .mark body => loopSurvives name body
  | .seq first second => loopSurvives name first ∧ loopSurvives name second
  | _ => True
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-- Cake `crep_to_loopProofScript.sml:368` `survives_MAPi_Assign`, stated for
    the `loopAssignPairs` numbering produced by the executable inliner. -/
theorem loopSurvives_loopAssignPairs (name : Nat) (names : List Nat)
    (expressions : List (LoopExp α)) (hlen : names.length = expressions.length) :
    loopSurvives name (loopNestedSeq (loopAssignPairs names expressions)) := by
  induction names generalizing expressions with
  | nil =>
      cases expressions with
      | nil => simp [loopAssignPairs, loopNestedSeq, loopSurvives]
      | cons expression expressions => simp at hlen
  | cons first rest ih =>
      cases expressions with
      | nil => simp at hlen
      | cons expression expressions =>
          simp only [loopAssignPairs_cons, loopNestedSeq, loopSurvives]
          exact ⟨trivial, ih expressions (by simpa using hlen)⟩

/-- Cake `crep_to_loopProofScript.sml:368`, for the `loopTempNames` numbering. -/
theorem loopSurvives_loopTempNames (name : Nat) (offset count : Nat)
    (expressions : List (LoopExp α))
    (hlen : (loopTempNames offset count).length = expressions.length) :
    loopSurvives name
      (loopNestedSeq (loopAssignPairs (loopTempNames offset count) expressions)) :=
  loopSurvives_loopAssignPairs name _ expressions hlen

/-- Cake's `survives_nested_seq_intro`
    (`cakeml/pancake/semantics/loopPropsScript.sml:719`): a variable surviving
    each of two statement lists also survives their concatenation. -/
theorem loopSurvives_nestedSeq_append (n : Nat)
    (statements rest : List (LoopProg α))
    (h1 : loopSurvives n (loopNestedSeq statements))
    (h2 : loopSurvives n (loopNestedSeq rest)) :
    loopSurvives n (loopNestedSeq (statements ++ rest)) := by
  revert h1 h2
  induction statements with
  | nil => intro h1 h2; simpa [loopNestedSeq] using h2
  | cons statement statements ih =>
      intro h1 h2
      rw [List.cons_append]
      simp only [loopNestedSeq, loopSurvives] at h1 ⊢
      exact ⟨h1.1, ih h1.2 h2⟩


def loopCompSyntaxOk (live : List Nat) : LoopProg α → Prop
  | .skip => True
  | .assign _ _ => True
  | .arith _ => True
  | .break _ => True
  | .locValue _ _ => True
  | .load32 _ _ => True
  | .loadByte _ _ => True
  | .seq first second =>
      loopCompSyntaxOk live first ∧ loopCompSyntaxOk (loopCutSets live first) second
  | .ite _ _ _ thenBranch elseBranch liveOut =>
      loopCompSyntaxOk live thenBranch ∧ loopCompSyntaxOk live elseBranch ∧
        ∃ ns : List Nat, liveOut = ns.foldl (fun current name => insertNatSorted name current) live
  | .loop liveIn body liveOut =>
      live = liveIn ∧ live = liveOut ∧ loopCompSyntaxOk liveIn body
  | _ => False

theorem loopCompSyntaxOk_seq2 (live : List Nat) (first second : LoopProg α)
    (h1 : loopCompSyntaxOk live first)
    (h2 : loopCompSyntaxOk (loopCutSets live first) second) :
    loopCompSyntaxOk live (.seq first second) :=
  ⟨h1, h2⟩

theorem loopCompSyntaxOk_nestedSeq_append (statements rest : List (LoopProg α))
    (live : List Nat)
    (h1 : loopCompSyntaxOk live (loopNestedSeq statements))
    (h2 : loopCompSyntaxOk (loopCutSets live (loopNestedSeq statements))
      (loopNestedSeq rest)) :
    loopCompSyntaxOk live (loopNestedSeq (statements ++ rest)) := by
  revert h1 h2
  induction statements generalizing live with
  | nil =>
      intro h1 h2
      simpa [loopNestedSeq, loopCutSets] using h2
  | cons statement statements ih =>
      intro h1 h2
      simp only [List.cons_append, loopNestedSeq, loopCompSyntaxOk] at h1 ⊢
      exact ⟨h1.1, ih (loopCutSets live statement) h1.2 h2⟩

theorem loopCompSyntaxOk_nestedSeq_append_elim (statements rest : List (LoopProg α))
    (live : List Nat)
    (h : loopCompSyntaxOk live (loopNestedSeq (statements ++ rest))) :
    loopCompSyntaxOk live (loopNestedSeq statements) ∧
      loopCompSyntaxOk (loopCutSets live (loopNestedSeq statements))
        (loopNestedSeq rest) := by
  induction statements generalizing live with
  | nil =>
      simp only [List.nil_append, loopNestedSeq, loopCutSets] at h ⊢
      exact ⟨trivial, h⟩
  | cons statement statements ih =>
      simp only [List.cons_append, loopNestedSeq, loopCompSyntaxOk] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨h2', h3⟩ := ih (loopCutSets live statement) h2
      exact ⟨⟨h1, h2'⟩, h3⟩

/-- Membership is preserved by a fold of `insertNatSorted`; this is the
    list-backed counterpart of CakeML's `union` accumulation used by
    `cut_sets_union_accumulate`. -/
theorem mem_foldl_insertNatSorted (names : List Nat) (live : List Nat) :
    ∀ x, x ∈ live →
      x ∈ names.foldl (fun current name => insertNatSorted name current) live := by
  induction names generalizing live with
  | nil => intro x hx; simpa using hx
  | cons name names ih =>
      intro x hx
      simp only [List.foldl_cons]
      exact ih (insertNatSorted name live) x
        (by rw [insertNatSorted_mem]; exact Or.inr hx)

/-- Cake's `cut_sets_union_domain_subset`
    (`cakeml/pancake/semantics/loopPropsScript.sml:810`) together with
    `comp_syn_impl_cut_sets_subspt` (`:831`): every variable already live
    before a syntactically well-formed statement remains live afterwards. -/
theorem loopCompSyntaxOk_cutSets_subset :
    ∀ (live : List Nat) (program : LoopProg α),
      loopCompSyntaxOk live program → ∀ x, x ∈ live → x ∈ loopCutSets live program := by
  apply loopCompSyntaxOk.induct (motive := fun live program =>
    loopCompSyntaxOk live program →
      ∀ x, x ∈ live → x ∈ loopCutSets live program)
  · intro live _ x hx; exact hx
  · intro live name value _ x hx; rw [loopCutSets, insertNatSorted_mem]; exact Or.inr hx
  · intro live operation h x hx; cases operation <;> simp only [loopCutSets] <;>
      first
        | (rw [insertNatSorted_mem]; exact Or.inr hx)
        | (rw [insertNatSorted_mem, insertNatSorted_mem]; exact Or.inr (Or.inr hx))
  · intro live label _ x hx; exact hx
  · intro live destination source _ x hx; rw [loopCutSets, insertNatSorted_mem]; exact Or.inr hx
  · intro live address destination _ x hx; rw [loopCutSets, insertNatSorted_mem]; exact Or.inr hx
  · intro live address destination _ x hx; rw [loopCutSets, insertNatSorted_mem]; exact Or.inr hx
  · intro live first second ihFirst ihSecond h x hx
    simp only [loopCutSets]
    exact ihSecond h.2 x (ihFirst h.1 x hx)
  · intro live operator condition right thenBranch elseBranch liveOut ihThen ihElse h x hx
    obtain ⟨_, _, ns, rfl⟩ := h
    simp only [loopCutSets]
    exact mem_foldl_insertNatSorted ns live x hx
  · intro live liveIn body liveOut ihBody h x hx
    obtain ⟨hlin, _, _⟩ := h
    subst hlin
    exact hx
  · intro t live h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h x hx
    exact absurd h (by cases t <;> simp_all [loopCompSyntaxOk])

/-- Membership in a fold of `insertNatSorted` is exactly membership in the
    initial live set or in the folded names; this is the list-backed
    counterpart of CakeML's `union` accumulation. -/
theorem mem_foldl_insertNatSorted_iff (names : List Nat) (live : List Nat) :
    ∀ x, x ∈ names.foldl (fun current name => insertNatSorted name current) live ↔
      x ∈ live ∨ x ∈ names := by
  induction names generalizing live with
  | nil => intro x; simp
  | cons name names ih =>
      intro x
      simp only [List.foldl_cons]
      rw [ih (insertNatSorted name live) x, insertNatSorted_mem]
      simp only [List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h

/-- Cake's `cut_sets_union_accumulate` (`cakeml/pancake/semantics/loopPropsScript.sml:777`)
    and `cut_sets_union_domain_union` (`:820`): the variables live after a
    syntactically well-formed statement are exactly the variables live before
    it together with a fresh set of names. -/
theorem loopCompSyntaxOk_cutSets_exists_extra :
    ∀ (live : List Nat) (program : LoopProg α),
      loopCompSyntaxOk live program →
        ∃ extra : List Nat,
          ∀ x, x ∈ loopCutSets live program ↔ x ∈ live ∨ x ∈ extra := by
  apply loopCompSyntaxOk.induct (motive := fun live program =>
    loopCompSyntaxOk live program →
      ∃ extra : List Nat,
        ∀ x, x ∈ loopCutSets live program ↔ x ∈ live ∨ x ∈ extra)
  · intro live _
    exact ⟨[], fun x => by simp [loopCutSets]⟩
  · intro live name value _
    exact ⟨[name], fun x => by
      rw [loopCutSets, insertNatSorted_mem]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h⟩
  · intro live operation _
    cases operation with
    | longMul dl dr sl sr =>
        exact ⟨[dl, dr], fun x => by
          rw [loopCutSets, insertNatSorted_mem, insertNatSorted_mem]
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | h | h)
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
            · exact Or.inl h
          · rintro (h | h | h)
            · exact Or.inr (Or.inr h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)⟩
    | longDiv dl dr sl sr q =>
        exact ⟨[dl, dr], fun x => by
          rw [loopCutSets, insertNatSorted_mem, insertNatSorted_mem]
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | h | h)
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
            · exact Or.inl h
          · rintro (h | h | h)
            · exact Or.inr (Or.inr h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)⟩
    | div d dd ds =>
        exact ⟨[d], fun x => by
          rw [loopCutSets, insertNatSorted_mem]
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | h)
            · exact Or.inr h
            · exact Or.inl h
          · rintro (h | h)
            · exact Or.inr h
            · exact Or.inl h⟩
  · intro live label _
    exact ⟨[], fun x => by simp [loopCutSets]⟩
  · intro live destination source _
    exact ⟨[destination], fun x => by
      rw [loopCutSets, insertNatSorted_mem]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h⟩
  · intro live address destination _
    exact ⟨[destination], fun x => by
      rw [loopCutSets, insertNatSorted_mem]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h⟩
  · intro live address destination _
    exact ⟨[destination], fun x => by
      rw [loopCutSets, insertNatSorted_mem]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h⟩
  · intro live first second ihFirst ihSecond h
    obtain ⟨e1, he1⟩ := ihFirst h.1
    obtain ⟨e2, he2⟩ := ihSecond h.2
    refine ⟨e1 ++ e2, fun x => ?_⟩
    simp only [loopCutSets]
    rw [he2 x, he1 x, List.mem_append]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  · intro live operator condition right thenBranch elseBranch liveOut ihThen ihElse h
    obtain ⟨_, _, ns, rfl⟩ := h
    exact ⟨ns, fun x => by
      simp only [loopCutSets]
      exact mem_foldl_insertNatSorted_iff ns live x⟩
  · intro live liveIn body liveOut ihBody h
    obtain ⟨hlin, _, _⟩ := h
    subst hlin
    exact ⟨[], fun x => by simp [loopCutSets]⟩
  · intro t live h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h
    exact absurd h (by cases t <;> simp_all [loopCompSyntaxOk])

theorem loopInsert_mem (name : Nat) (names : List Nat) (x : Nat) :
    x ∈ loopInsert name names ↔ x = name ∨ x ∈ names := by
  by_cases hname : name ∈ names
  · rw [loopInsert, if_pos hname]
    exact ⟨fun h => Or.inr h, fun h => h.elim (fun heq => heq ▸ hname) id⟩
  · rw [loopInsert, if_neg hname]
    exact List.mem_cons

theorem loopInsertAll_mem (added : List Nat) (names : List Nat) (x : Nat) :
    x ∈ loopInsertAll added names ↔ x ∈ added ∨ x ∈ names := by
  induction added generalizing names with
  | nil => simp [loopInsertAll]
  | cons name rest ih =>
      simp only [loopInsertAll]
      rw [loopInsert_mem name (loopInsertAll rest names) x, ih names]
      simp only [List.mem_cons]
      constructor
      · rintro (h | (h | h))
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

set_option linter.unusedSimpArgs false in
private theorem loopAccVars_mem_aux : ∀ (program : LoopProg α) (_acc : List Nat)
    (names : List Nat) (x : Nat),
    x ∈ loopAccVars program names ↔ x ∈ names ∨ x ∈ loopAccVars program [] := by
  apply loopAccVars.induct (motive := fun program _ =>
    ∀ names x, x ∈ loopAccVars program names ↔ x ∈ names ∨ x ∈ loopAccVars program [])
  · intro first second names ihSecond ihFirst names' x
    simp only [loopAccVars]
    rw [ihFirst (loopAccVars second names') x, ihFirst (loopAccVars second []) x,
      ihSecond names' x, ihSecond [] x]
    simp only [List.not_mem_nil, or_false]
    simp only [or_comm, or_left_comm]
  · intro label names names' x; simp [loopAccVars]
  · intro label names names' x; simp [loopAccVars]
  · intro liveIn body liveOut names ih names' x
    simp only [loopAccVars]; exact ih names' x
  · intro operator condition right thenBranch elseBranch live names ihElse ihThen names' x
    simp only [loopAccVars]
    rw [ihThen (loopAccVars elseBranch names') x, ihThen (loopAccVars elseBranch []) x,
      ihElse names' x, ihElse [] x]
    simp only [List.not_mem_nil, or_false]
    simp only [or_comm, or_left_comm]
  · intro names left right sourceLeft sourceRight names' x
    simp only [loopAccVars, loopInsertAll_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro names left right sourceLeft sourceRight quotient names' x
    simp only [loopAccVars, loopInsertAll_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro names destination dividend divisor names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro body names ih names' x
    simp only [loopAccVars]; exact ih names' x
  · intro names names' x; simp [loopAccVars]
  · intro names names' x; simp [loopAccVars]
  · intro names names' x; simp [loopAccVars]
  · intro exception names names' x; simp [loopAccVars]
  · intro values names names' x; simp [loopAccVars]
  · intro target arguments handler names names' x; simp [loopAccVars]
  · intro returns snd target arguments names names' x
    simp only [loopAccVars, loopInsertAll_mem, List.not_mem_nil, or_false]
    simp only [or_comm, or_left_comm]
  · intro returns snd target arguments exception handler normal snd_1 names ihNormal ihHandler names' x
    simp only [loopAccVars, loopInsert_mem, loopInsertAll_mem]
    rw [ihHandler (loopAccVars normal names') x, ihHandler (loopAccVars normal []) x,
      ihNormal names' x, ihNormal [] x]
    simp only [List.not_mem_nil, or_false, false_or]
    simp only [or_comm, or_left_comm]
  · intro destination _label names names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro destination value names names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro destinations operator arguments names names' x
    simp only [loopAccVars, loopInsertAll_mem, List.not_mem_nil, or_false]
    simp only [or_comm, or_left_comm]
  · intro operator destination address names names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro address value names names' x; simp [loopAccVars]
  · intro address value names names' x; simp [loopAccVars]
  · intro address destination names names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro address destination names names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro address value names names' x; simp [loopAccVars]
  · intro address value names names' x; simp [loopAccVars]
  · intro function configuration configurationLength array arrayLength live names names' x
    simp [loopAccVars]

theorem loopAccVars_mem (program : LoopProg α) (names : List Nat) (x : Nat) :
    x ∈ loopAccVars program names ↔ x ∈ names ∨ x ∈ loopAccVars program [] :=
  loopAccVars_mem_aux program names names x


end Flapjack
