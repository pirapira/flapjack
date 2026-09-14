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
      if name == head then tail else head :: deleteNatSorted name tail

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
      (.ite operator condition right then' else' branchLive,
        insertNatSorted condition
          (loopListInsert rightLive (thenLive ++ elseLive)))
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
      /- Cake's `fixedpoint` repeats the body shrink with the loop's output
         live set until the live-in set stabilizes.  The bound is an
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
            let (body', bodyLive) := loopShrinkLeaf body loopLiveOut
            let current := loopIntersectSorted liveIn bodyLive
            if current = previous then
              (.loop current body' loopLiveOut, current)
            else if current.length ≤ previous.length then
              let (fallback, _) := loopShrinkLeaf body bodyEntryLive
              (.loop liveIn fallback loopLiveOut, liveIn)
            else
              fixedpoint fuel current
      fixedpoint 32 []
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
      (.ite operator condition right then' else' branchLive,
        insertNatSorted condition (loopListInsert rightLive (thenLive ++ elseLive)))
  | .mark body, live => loopShrink contexts body live
  | .break label, _ =>
      (.break label, (loopContextAt label contexts).map Prod.snd |>.getD [])
  | .continue label, _ =>
      (.continue label, (loopContextAt label contexts).map Prod.fst |>.getD [])
  | .loop liveIn body liveOut, live =>
      let loopLiveOut := loopIntersectSorted liveOut live
      let bodyEntryLive := loopListInsert liveIn loopLiveOut
      match loopShrinkFixed contexts liveIn body loopLiveOut 64 [] with
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
    (liveIn : List Nat) (body : LoopProg α) (loopLiveOut : List Nat) :
    Nat → List Nat → Option (LoopProg α × List Nat)
  | 0, _ => none
  | fuel + 1, previous =>
      let (body', bodyLive) := loopShrink
        ((loopIntersectSorted liveIn previous, loopLiveOut) :: contexts)
        body loopLiveOut
      let current := loopIntersectSorted liveIn bodyLive
      if current = previous then
        some (.loop current body' loopLiveOut, current)
      else if current.length ≤ previous.length then
        none
      else
        loopShrinkFixed contexts liveIn body loopLiveOut fuel current
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
  | .ite _ condition right thenBranch elseBranch _, names =>
      let names := loopAccVars thenBranch (loopAccVars elseBranch names)
      loopInsert condition (match right with | .reg value => value :: names | .imm _ => names)
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

end Flapjack
